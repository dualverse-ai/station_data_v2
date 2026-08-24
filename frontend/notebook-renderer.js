import { Widget } from '@lumino/widgets';
import {
  CodeMirrorEditorFactory,
  CodeMirrorMimeTypeService,
  EditorExtensionRegistry,
  EditorLanguageRegistry,
  EditorThemeRegistry
} from '@jupyterlab/codemirror';
import { MathJaxTypesetter } from '@jupyterlab/mathjax-extension';
import { createMarkdownParser } from '@jupyterlab/markedparser-extension';
import { NotebookModel, StaticNotebook } from '@jupyterlab/notebook';
import { RenderMimeRegistry, standardRendererFactories } from '@jupyterlab/rendermime';

import '@lumino/widgets/style/index.css';
import '@jupyterlab/ui-components/style/base.css';
import '@jupyterlab/apputils/style/base.css';
import '@jupyterlab/rendermime/style/base.css';
import '@jupyterlab/codeeditor/style/base.css';
import '@jupyterlab/codemirror/style/base.css';
import '@jupyterlab/outputarea/style/base.css';
import '@jupyterlab/cells/style/base.css';
import '@jupyterlab/notebook/style/base.css';
import '@jupyterlab/mathjax-extension/style/base.css';

function editorServices() {
  const languages = new EditorLanguageRegistry();
  EditorLanguageRegistry.getDefaultLanguages()
    .filter(language => ['Python', 'ipython', 'Markdown'].includes(language.name))
    .forEach(language => languages.addLanguage(language));

  const themes = new EditorThemeRegistry();
  const extensions = new EditorExtensionRegistry();
  EditorExtensionRegistry.getDefaultExtensions({ themes })
    .forEach(extension => extensions.addExtension(extension));
  const factory = new CodeMirrorEditorFactory({ languages, extensions });
  return {
    editorFactory: factory.newInlineEditor.bind(factory),
    languages,
    mimeTypeService: new CodeMirrorMimeTypeService(languages)
  };
}

function collapseCodeCells(host) {
  host.querySelectorAll('.jp-CodeCell').forEach((cell, index) => {
    if (cell.querySelector(':scope > .notebook-code-toggle')) return;
    const input = cell.querySelector('.jp-Cell-inputWrapper');
    if (!input) return;

    const button = document.createElement('button');
    const inputId = `notebook-code-input-${index + 1}`;
    input.id = inputId;
    cell.classList.add('notebook-code-collapsed');
    button.type = 'button';
    button.className = 'notebook-code-toggle';
    button.textContent = 'Show code';
    button.setAttribute('aria-controls', inputId);
    button.setAttribute('aria-expanded', 'false');
    button.addEventListener('click', () => {
      const collapsed = cell.classList.toggle('notebook-code-collapsed');
      button.textContent = collapsed ? 'Show code' : 'Hide code';
      button.setAttribute('aria-expanded', String(!collapsed));
    });
    cell.insertBefore(button, input);
  });
}

function nextTurn() {
  return new Promise(resolve => setTimeout(resolve, 0));
}

async function waitForCells(host, expected, attempts = 120) {
  for (let attempt = 0; attempt < attempts; attempt += 1) {
    if (host.querySelectorAll('.jp-Cell').length >= expected) return true;
    await new Promise(resolve => setTimeout(resolve, 50));
  }
  return false;
}

function normalizeNotebookJSON(value) {
  const notebook = structuredClone(value);
  for (const cell of notebook.cells || []) {
    if (Array.isArray(cell.source)) cell.source = cell.source.join('');
    for (const output of cell.outputs || []) {
      if (Array.isArray(output.text)) output.text = output.text.join('');
      for (const [mimeType, data] of Object.entries(output.data || {})) {
        if (Array.isArray(data) && data.every(part => typeof part === 'string')) {
          output.data[mimeType] = data.join('');
        }
      }
    }
  }
  return notebook;
}

async function findAnchor(host, anchor, attempts = 80) {
  if (!anchor) return null;
  const escaped = CSS.escape(anchor);
  for (let attempt = 0; attempt < attempts; attempt += 1) {
    const target = host.querySelector(`#${escaped}, [data-jupyter-id="${escaped}"]`);
    if (target) return target;
    await new Promise(resolve => setTimeout(resolve, 50));
  }
  return null;
}

async function render(host, notebookJSON) {
  if (!(host instanceof HTMLElement)) throw new TypeError('Notebook host must be an HTML element');
  const services = editorServices();
  const markdownParser = createMarkdownParser(services.languages);
  const rendermime = new RenderMimeRegistry({
    initialFactories: standardRendererFactories,
    latexTypesetter: new MathJaxTypesetter(),
    markdownParser
  });
  const contentFactory = new StaticNotebook.ContentFactory({ editorFactory: services.editorFactory });
  const notebook = new StaticNotebook({
    contentFactory,
    editorConfig: StaticNotebook.defaultEditorConfig,
    mimeTypeService: services.mimeTypeService,
    notebookConfig: {
      ...StaticNotebook.defaultNotebookConfig,
      windowingMode: 'none'
    },
    rendermime
  });
  const model = new NotebookModel({ languagePreference: 'python' });
  model.fromJSON(normalizeNotebookJSON(notebookJSON));
  model.readOnly = true;
  notebook.model = model;
  const observer = new MutationObserver(() => collapseCodeCells(host));
  observer.observe(host, { childList: true, subtree: true });
  Widget.attach(notebook, host);
  await nextTurn();
  if (!await waitForCells(host, model.cells.length)) {
    notebook.dispose();
    model.dispose();
    observer.disconnect();
    throw new Error('Notebook cells did not finish rendering');
  }
  collapseCodeCells(host);

  return {
    async scrollTo(anchor) {
      if (!await findAnchor(host, anchor)) return false;
      await document.fonts?.ready;
      let stableFrames = 0;
      let previousHeight = -1;
      for (let attempt = 0; attempt < 40 && stableFrames < 3; attempt += 1) {
        const target = await findAnchor(host, anchor, 1);
        if (!target) { stableFrames = 0; continue; }
        target.scrollIntoView({ block: 'start' });
        await new Promise(resolve => setTimeout(resolve, 100));
        const height = host.scrollHeight;
        const aligned = Math.abs(target.getBoundingClientRect().top) < 2;
        stableFrames = aligned && height === previousHeight ? stableFrames + 1 : 0;
        previousHeight = height;
      }
      (await findAnchor(host, anchor, 1))?.scrollIntoView({ block: 'start' });
      return true;
    },
    dispose() {
      observer.disconnect();
      notebook.dispose();
      model.dispose();
    }
  };
}

window.StationNotebookRenderer = Object.freeze({ render });
