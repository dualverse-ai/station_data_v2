/* Read-only Station V2 viewer. */
(() => {
  'use strict';

  const app = document.getElementById('app');
  const navbar = document.getElementById('navbar');
  const navLinks = document.getElementById('nav-links');
  const stationSelector = document.getElementById('station-selector');
  const endTick = document.getElementById('end-tick');
  const themeToggle = document.getElementById('theme-toggle');
  const mobileToggle = document.getElementById('mobile-menu-toggle');
  const backdrop = document.getElementById('mobile-menu-backdrop');
  const githubRoot = 'https://github.com/dualverse-ai/station_data_v2';
  const rawRoot = document.querySelector('meta[name="station-archive-root"]')?.content || '';
  const archiveRoot = location.hostname.endsWith('.github.io') ? rawRoot : '';
  const state = { catalog: null, request: 0, controller: null, graphCleanup: null, notebookCleanup: null, cache: new Map() };
  const capsuleLabels = {
    archive: 'Archive Paper', public: 'Public Memory Capsule', private: 'Private Memory Capsule',
    mail: 'Mail', question: 'Questions'
  };

  function escapeHtml(value) {
    const node = document.createElement('span');
    node.textContent = String(value ?? '');
    return node.innerHTML;
  }
  function archiveUrl(path) { return `${archiveRoot}${String(path).replace(/^\/+/, '')}`; }
  function encodePath(path) { return String(path).split('/').map(encodeURIComponent).join('/'); }
  function stationUrl(id, page = 'agents') { return `#/${encodeURIComponent(id)}/${page}`; }
  function dialogueTickUrl(stationId, agentKey, tick, thinkingOpen = false) {
    const query = new URLSearchParams({ tick: String(tick) });
    if (thinkingOpen) query.set('thinking', 'open');
    return `#/${encodeURIComponent(stationId)}/agent/${encodeURIComponent(agentKey)}?${query}`;
  }
  function parseDialogueTarget(query) {
    if (!query.has('tick')) return null;
    const tick = query.get('tick')?.trim() || '';
    if (!/^\d+$/.test(tick)) throw new Error('Dialogue tick must be a non-negative integer');
    return { tick, thinkingOpen: query.get('thinking') === 'open' };
  }
  function notebookUrl(id, path, section = '') { return `#/notebooks/${encodeURIComponent(id)}/${encodeURIComponent(path)}${section ? `/${encodeURIComponent(section)}` : ''}`; }
  function githubTree(path) { return `${githubRoot}/tree/main/${encodePath(path)}`; }
  function githubFile(path) { return `${githubRoot}/blob/main/${encodePath(path)}`; }
  function bundleFile(id) { return `${archiveRoot ? '' : '_site/'}bundles/${encodeURIComponent(id)}.zip`; }
  function current(request) {
    if (request !== state.request) throw new DOMException('Stale route', 'AbortError');
  }

  function repairStationCodeFences(source) {
    const pattern = /(^### Message \d+[^\n]*\n+\*\*(?:Storage|Code) Read:\*\*[^\n]*\n+)(`{3,})([^\n]*)\n([\s\S]*?)\n`{3,}[ \t]*(?=\n+(?:### Message \d+[^\n]*\n|---\n+## Actions Detected))/gm;
    return String(source || '').replace(pattern, (_match, prefix, _opening, info, body) => {
      const nested = body.match(/`{3,}/g) || [];
      const width = Math.max(3, ...nested.map(run => run.length)) + 1;
      const fence = '`'.repeat(width);
      const extension = prefix.match(/`[^`]+\.([A-Za-z0-9]+)`/)?.[1]?.toLowerCase();
      const languages = {
        json: 'json', yaml: 'yaml', yml: 'yaml', py: 'python', md: 'markdown',
        c: 'c', cc: 'cpp', cpp: 'cpp', h: 'c', hpp: 'cpp', js: 'javascript',
        ts: 'typescript', sh: 'bash'
      };
      const label = info.trim() || languages[extension] || '';
      return `${prefix}${fence}${label}\n${body}\n${fence}`;
    });
  }
  function normalizeStationActions(source) {
    let text = String(source || '');
    const held = [];
    const protect = value => { const token = `@@ACTION_CODE_${held.length}@@`; held.push(value); return token; };
    text = text.replace(/(^|\n)([ \t]*)(`{3,}|~{3,})[^\n]*\n[\s\S]*?\n\2\3[ \t]*(?=\n|$)/g, protect);
    text = text.replace(/(`+)([^`\n]*?)\1/g, protect);
    text = text.replace(/\/execute_action\{[^}\n]+\}/g, command => `\`${command}\``);
    return text.replace(/@@ACTION_CODE_(\d+)@@/g, (_match, index) => held[Number(index)] || '');
  }
  function styleStationActions(html) {
    return String(html || '').replace(
      /<code>(\/execute_action\{[\s\S]*?\})<\/code>/g,
      (_match, command) => {
        const verb = command.match(/^\/execute_action\{\s*([a-zA-Z_]+)/)?.[1]?.toLowerCase() || 'action';
        const body = command.match(/^\/execute_action\{([\s\S]*)\}$/)?.[1]?.trim() || command;
        const navigation = new Set(['goto']);
        const reads = new Set(['read', 'read_task', 'read_code', 'review', 'preview', 'rank', 'filter', 'unfilter', 'storage', 'page', 'page_size', 'help']);
        const writes = new Set(['submit', 'create', 'reply', 'update', 'forward', 'meta', 'speak', 'survey', 'reflect', 'request_human']);
        const category = navigation.has(verb) ? 'navigation' : reads.has(verb) ? 'read' : writes.has(verb) ? 'write' : 'control';
        return `<code class="station-action-command station-action-${category}" data-station-action-verb="${verb}">${body}</code>`;
      }
    );
  }
  const yamlActionLabels = {
    submit: 'Research Submission', reply: 'Capsule Reply', create: 'Capsule Creation',
    meta: 'Agent Meta Prompt', speak: 'Common Room Post', reflect: 'Reflection',
    survey: 'Archive Survey Request', request_human: 'Human Assistance Request'
  };
  const yamlMarkdownFields = [['abstract', 'Abstract'], ['content', 'Content'], ['message', 'Message'], ['description', 'Description'], ['prompt', 'Prompt']];
  const yamlCardLimit = 120000;
  function yamlActionHint(source, offset) {
    const match = source.slice(Math.max(0, offset - 320), offset).match(/(?:^|\n)\s*`?\/execute_action\{([^}\n]+)\}`?\s*$/i);
    return match ? String(match[1]).trim().split(/\s+/)[0].toLowerCase() : '';
  }
  function parseYamlCard(rawYaml, hint) {
    if (!window.jsyaml || !rawYaml || rawYaml.length > yamlCardLimit) return null;
    try {
      const parsed = window.jsyaml.load(rawYaml, { schema: window.jsyaml.FAILSAFE_SCHEMA, json: false });
      if (!parsed || Object.prototype.toString.call(parsed) !== '[object Object]') return null;
      const hasText = ['title', 'content', 'abstract', 'instruction', 'message', 'description', 'prompt'].some(key => typeof parsed[key] === 'string');
      const resemblesSubmission = ['title', 'abstract', 'instruction'].every(key => typeof parsed[key] === 'string');
      const resemblesCapsule = typeof parsed.title === 'string' && typeof parsed.content === 'string';
      return Object.keys(parsed).length && hasText && (yamlActionLabels[hint] || resemblesSubmission || resemblesCapsule) ? parsed : null;
    } catch (_error) { return null; }
  }
  function safeMarkdownInline(value) {
    if (!window.marked || !window.DOMPurify) return escapeHtml(value);
    const html = window.marked.parseInline(normalizeMath(String(value || '')), { gfm: true, breaks: false });
    return window.DOMPurify.sanitize(html, { USE_PROFILES: { html: true, mathMl: true }, FORBID_TAGS: ['style'] });
  }
  function renderYamlCard(parsed, rawYaml, hint) {
    const actionLabel = yamlActionLabels[hint] || (typeof parsed.instruction === 'string' ? 'Research Submission' : 'Structured Station Action');
    const title = typeof parsed.title === 'string' && parsed.title.trim() ? parsed.title.trim() : actionLabel;
    const eyebrow = title === actionLabel ? 'Station Action' : actionLabel;
    const tags = Array.isArray(parsed.tags) ? parsed.tags.map(String) : String(parsed.tags || '').split(',');
    const cleanTags = tags.map(tag => tag.trim()).filter(Boolean);
    const fields = yamlMarkdownFields.map(([key, label]) => {
      if (typeof parsed[key] !== 'string' || !parsed[key].trim()) return '';
      return `<section class="station-yaml-field"><div class="station-yaml-field-label">${label}</div><div class="station-yaml-field-markdown">${markdown(parsed[key], { enhanceYamlCards: false })}</div></section>`;
    }).join('');
    const instructions = typeof parsed.instruction === 'string' && parsed.instruction.trim()
      ? `<details class="station-yaml-instructions" open><summary>Full instructions</summary><div class="station-yaml-field-markdown">${markdown(parsed.instruction, { enhanceYamlCards: false })}</div></details>` : '';
    return `<article class="station-yaml-card" data-station-action="${escapeHtml(hint || 'structured')}"><header class="station-yaml-card-header"><div class="station-yaml-card-heading"><div class="station-yaml-card-eyebrow">${escapeHtml(eyebrow)}</div><div class="station-yaml-card-title">${safeMarkdownInline(title)}</div></div><button type="button" class="station-yaml-copy-button">Copy YAML</button></header>${cleanTags.length ? `<div class="station-yaml-tags">${cleanTags.map(tag => `<span>${escapeHtml(tag)}</span>`).join('')}</div>` : ''}<div class="station-yaml-card-body">${fields}${instructions}</div><textarea class="station-yaml-copy-source" hidden readonly aria-hidden="true">${escapeHtml(rawYaml)}</textarea></article>`;
  }
  function holdEmbedded(html, embedded) {
    const index = embedded.length; embedded.push(html); return `\n\nSTATIONEMBEDDEDHTML${index}TOKEN\n\n`;
  }
  function restoreEmbedded(html, embedded) {
    let result = String(html || '');
    embedded.forEach((value, index) => {
      const token = `STATIONEMBEDDEDHTML${index}TOKEN`;
      result = result.replace(new RegExp(`<p>\\s*${token}\\s*</p>`, 'g'), value).split(token).join(value);
    });
    return result;
  }
  function enhanceYamlFences(source, embedded) {
    return String(source || '').replace(/(^|\n)[ \t]*```ya?ml[ \t]*\r?\n([\s\S]*?)\r?\n[ \t]*```(?=\n|$)/gi, (match, leading, rawYaml, offset) => {
      const hint = yamlActionHint(source, offset); const parsed = parseYamlCard(rawYaml, hint);
      return parsed ? `${leading}${holdEmbedded(renderYamlCard(parsed, rawYaml, hint), embedded)}\n` : match;
    });
  }
  function enhanceBareYamlActions(source, embedded) {
    let text = String(source || ''); const protectedCode = [];
    text = text.replace(/(^|\n)([ \t]*)(`{3,}|~{3,})[^\n]*\n[\s\S]*?\n\2\3[ \t]*(?=\n|$)/g, value => {
      const token = `STATIONBAREYAMLCODE${protectedCode.length}TOKEN`; protectedCode.push(value); return token;
    });
    const pattern = /(^|\n)[ \t]*`?\/execute_action\{([^}\n]+)\}`?[ \t]*\r?\n/g;
    let result = ''; let cursor = 0; let match;
    while ((match = pattern.exec(text)) !== null) {
      if (match.index < cursor) continue;
      const hint = String(match[2] || '').trim().split(/\s+/)[0].toLowerCase();
      if (!yamlActionLabels[hint]) continue;
      let start = pattern.lastIndex; start += text.slice(start).match(/^(?:[ \t]*\r?\n)*/)?.[0].length || 0;
      const remaining = text.slice(start); if (!/^[A-Za-z_][A-Za-z0-9_-]*[ \t]*:/.test(remaining)) continue;
      const lines = remaining.match(/.*(?:\r?\n|$)/g) || []; let used = 0; let end = -1;
      for (let index = 0; index < lines.length; index += 1) {
        used += lines[index].length; const next = lines[index + 1] || ''; const plain = next.replace(/\r?\n$/, '');
        if (next && (!plain.trim() || /^[ \t]/.test(plain) || /^[A-Za-z_][A-Za-z0-9_-]*[ \t]*:/.test(plain) || /^-[ \t]+/.test(plain) || /^#/.test(plain))) continue;
        if (parseYamlCard(remaining.slice(0, used).trimEnd(), hint)) end = start + remaining.slice(0, used).trimEnd().length;
        break;
      }
      if (end < start) continue;
      const rawYaml = text.slice(start, end); const parsed = parseYamlCard(rawYaml, hint); if (!parsed) continue;
      result += text.slice(cursor, start) + `${holdEmbedded(renderYamlCard(parsed, rawYaml, hint), embedded)}\n`; cursor = end; pattern.lastIndex = end;
    }
    if (cursor) text = result + text.slice(cursor);
    return text.replace(/STATIONBAREYAMLCODE(\d+)TOKEN/g, (_match, index) => protectedCode[Number(index)] || '');
  }
  function normalizeMath(source) {
    const held = [];
    const protect = value => { const token = `@@CODE_${held.length}@@`; held.push(value); return token; };
    let text = normalizeStationActions(repairStationCodeFences(source));
    text = text.replace(/(^|\n)([ \t]*)(`{3,}|~{3,})[^\n]*\n[\s\S]*?\n\2\3[ \t]*(?=\n|$)/g, protect);
    text = text.replace(/(`+)([^`\n]*?)\1/g, protect);
    text = text.replace(/\\\[([\s\S]*?)\\\]/g, (_m, formula) => `$$${String(formula).replace(/\r?\n[ \t]*/g, ' ').trim()}$$`);
    text = text.replace(/\\\(([\s\S]*?)\\\)/g, (_m, formula) => `$${formula}$`);
    return text.replace(/@@CODE_(\d+)@@/g, (_m, n) => held[Number(n)] || '');
  }
  function configureMarkdown() {
    if (!window.marked) return;
    const renderer = new window.marked.Renderer();
    renderer.html = html => escapeHtml(html);
    window.marked.use({ renderer });
    const extension = window.markedKatex && (window.markedKatex.default || window.markedKatex);
    if (extension && window.katex) window.marked.use(extension({ throwOnError: false, nonStandard: true, strict: 'ignore', trust: false }));
    window.marked.setOptions({ gfm: true, breaks: true });
  }
  function markdown(value, options = {}) {
    let source = normalizeMath(value); const embedded = [];
    if (options.enhanceYamlCards !== false) {
      source = enhanceYamlFences(source, embedded);
      source = enhanceBareYamlActions(source, embedded);
    }
    if (!window.marked || !window.DOMPurify) return `<pre>${escapeHtml(source)}</pre>`;
    const html = styleStationActions(window.marked.parse(source));
    const clean = window.DOMPurify.sanitize(html, { USE_PROFILES: { html: true, mathMl: true }, FORBID_TAGS: ['style'] });
    return `<div class="markdown-content-host">${restoreEmbedded(clean, embedded)}</div>`;
  }
  async function copyText(value) {
    if (navigator.clipboard?.writeText) { await navigator.clipboard.writeText(String(value)); return; }
    const field = document.createElement('textarea'); field.value = String(value); field.style.position = 'fixed'; field.style.opacity = '0';
    document.body.appendChild(field); field.select(); document.execCommand('copy'); field.remove();
  }
  function enhance(root = app) {
    root.querySelectorAll('.markdown-content-host pre code').forEach(code => window.hljs?.highlightElement(code));
    root.querySelectorAll('.markdown-content-host a').forEach(link => {
      if (/^https?:/i.test(link.getAttribute('href') || '')) { link.target = '_blank'; link.rel = 'noopener noreferrer'; }
    });
    root.querySelectorAll('.station-yaml-copy-button:not([data-bound])').forEach(button => {
      button.dataset.bound = 'true'; button.addEventListener('click', async () => {
        const source = button.closest('.station-yaml-card')?.querySelector('.station-yaml-copy-source')?.value || '';
        await copyText(source); button.textContent = 'Copied'; setTimeout(() => { button.textContent = 'Copy YAML'; }, 1200);
      });
    });
  }

  async function fetchJSON(path, signal) {
    const response = await fetch(archiveUrl(path), { signal, cache: 'no-cache' });
    if (!response.ok) throw new Error(`Could not load ${path} (${response.status})`);
    return response.json();
  }
  async function fetchGzip(path, signal) {
    if (state.cache.has(path)) return state.cache.get(path);
    const response = await fetch(archiveUrl(path), { signal });
    if (!response.ok) throw new Error(`Could not load ${path} (${response.status})`);
    if (!response.body || typeof DecompressionStream === 'undefined') throw new Error('A current browser with gzip streaming support is required.');
    const text = await new Response(response.body.pipeThrough(new DecompressionStream('gzip'))).text();
    state.cache.set(path, text);
    if (state.cache.size > 16) state.cache.delete(state.cache.keys().next().value);
    return text;
  }

  function setTheme(theme) {
    const value = theme === 'dark' ? 'dark' : 'light';
    document.documentElement.dataset.theme = value;
    themeToggle.textContent = value === 'light' ? 'Switch to dark mode' : 'Switch to light mode';
    localStorage.setItem('station-viewer-theme', value);
  }
  function closeMenu() {
    navLinks.classList.remove('open'); backdrop.classList.remove('open');
    mobileToggle.setAttribute('aria-expanded', 'false'); mobileToggle.setAttribute('aria-label', 'Open navigation menu');
  }
  function stationById(id) { return state.catalog.stations.find(station => station.id === id); }
  function showNavbar(station, page) {
    navbar.hidden = !station;
    if (!station) return;
    stationSelector.value = station.id;
    endTick.textContent = station.tick ?? '—';
    navLinks.querySelectorAll('[data-page]').forEach(link => {
      const target = link.dataset.page;
      link.href = stationUrl(station.id, target === 'public' || target === 'private' ? `memory/${target}` : target);
      link.classList.toggle('active', page === target);
    });
  }
  function pageHeader(title, subtitle = '', action = '') {
    return `<header class="page-header"><div><h1>${escapeHtml(title)}</h1>${subtitle ? `<p>${escapeHtml(subtitle)}</p>` : ''}</div>${action}</header>`;
  }
  function meta(items) {
    return `<div class="metadata-grid">${items.map(([label, value]) => `<div class="metadata-item"><span>${escapeHtml(label)}</span><strong>${escapeHtml(value ?? '—')}</strong></div>`).join('')}</div>`;
  }
  const naturalOrder = new Intl.Collator(undefined, { numeric: true, sensitivity: 'base' });
  function capsuleDisplayId(value) {
    const match = String(value ?? '').match(/_(\d+)$/);
    return match ? match[1] : String(value ?? '');
  }
  function reviewScore(value) {
    const number = Number(value);
    return Number.isFinite(number) ? `${Number.isInteger(number) ? number : number.toFixed(2).replace(/0+$/, '').replace(/\.$/, '')}/10` : '—';
  }
  function statusBadge(value) {
    const status = String(value || 'pending').toLowerCase();
    const safe = ['pending', 'open', 'redacted', 'solved', 'retired'].includes(status) ? status : 'pending';
    return `<span class="question-status status-${safe}">${escapeHtml(safe)}</span>`;
  }
  function sortedRecords(records, sort, accessors = {}) {
    const value = item => accessors[sort.key] ? accessors[sort.key](item) : item[sort.key];
    return [...records].sort((left, right) => {
      const a = value(left); const b = value(right);
      const aMissing = a === null || a === undefined || a === '' || a === 'n.a.';
      const bMissing = b === null || b === undefined || b === '' || b === 'n.a.';
      if (aMissing !== bMissing) return aMissing ? 1 : -1;
      if (aMissing) return 0;
      const aNumber = typeof a === 'number' ? a : (/^-?\d+(?:\.\d+)?$/.test(String(a)) ? Number(a) : null);
      const bNumber = typeof b === 'number' ? b : (/^-?\d+(?:\.\d+)?$/.test(String(b)) ? Number(b) : null);
      const order = aNumber !== null && bNumber !== null ? aNumber - bNumber : naturalOrder.compare(String(a), String(b));
      return sort.direction === 'asc' ? order : -order;
    });
  }
  function sortableHeaders(columns, sort) {
    return columns.map(([key, label]) => {
      const active = sort.key === key;
      return `<th class="sortable${active ? ` sort-${sort.direction}` : ''}" data-sort="${escapeHtml(key)}" tabindex="0" aria-sort="${active ? (sort.direction === 'asc' ? 'ascending' : 'descending') : 'none'}">${escapeHtml(label)}</th>`;
    }).join('');
  }
  function mobileSortControls(columns, sort) {
    return `<div class="mobile-sort-controls"><label>Sort by <select class="mobile-sort-select">${columns.map(([key, label]) => `<option value="${escapeHtml(key)}"${sort.key === key ? ' selected' : ''}>${escapeHtml(label)}</option>`).join('')}</select></label><button class="button mobile-sort-direction" type="button" aria-label="Reverse sort order">${sort.direction === 'asc' ? 'Ascending ↑' : 'Descending ↓'}</button></div>`;
  }
  function bindSorting(container, sort, draw) {
    const change = header => {
      const key = header?.dataset.sort; if (!key) return;
      if (sort.key === key) sort.direction = sort.direction === 'asc' ? 'desc' : 'asc';
      else { sort.key = key; sort.direction = 'asc'; }
      draw();
    };
    container.addEventListener('click', event => {
      const header = event.target.closest('th.sortable');
      if (header) change(header);
      else if (event.target.closest('.mobile-sort-direction')) { sort.direction = sort.direction === 'asc' ? 'desc' : 'asc'; draw(); }
    });
    container.addEventListener('change', event => {
      if (!event.target.matches('.mobile-sort-select')) return;
      sort.key = event.target.value; sort.direction = 'asc'; draw();
    });
    container.addEventListener('keydown', event => {
      if ((event.key === 'Enter' || event.key === ' ') && event.target.matches('th.sortable')) { event.preventDefault(); change(event.target); }
    });
  }
  function bindRowLinks(container) {
    container.addEventListener('click', event => {
      if (event.target.closest('a, button, input, select')) return;
      const row = event.target.closest('tr[data-href]');
      if (row?.dataset.href) location.href = row.dataset.href;
    });
  }

  function renderDashboard() {
    showNavbar(null);
    const stations = [...state.catalog.stations].sort((left, right) => naturalOrder.compare(left.title, right.title));
    app.innerHTML = `<section class="dashboard">
      <img class="dashboard-logo" src="images/logo.png" alt="Station">
      <h1>Select a station to explore</h1>
      <div class="station-grid">${stations.map(station => `<a class="station-card" href="${stationUrl(station.id)}"><h2>${escapeHtml(station.title)}</h2><p>End Tick: ${escapeHtml(station.tick ?? '—')}</p></a>`).join('')}</div>
      <p class="dashboard-links"><a href="#/notebooks">Verification notebooks</a><span aria-hidden="true">·</span><a href="https://dualverse-ai.github.io/station_data/" target="_blank" rel="noopener noreferrer">Station Viewer v1</a></p>
    </section>`;
  }

  async function renderAgents(station, signal, request) {
    const data = await fetchJSON(`data/${station.id}/agents/index.json`, signal); current(request);
    const agents = data.agents || [];
    app.innerHTML = `${pageHeader('Agent Dialogue')}<div class="toolbar"><label class="sr-only" for="search">Search agents</label><input id="search" type="search" placeholder="Search agents"></div><div id="results"></div>`;
    const search = document.getElementById('search');
    const results = document.getElementById('results');
    const sort = { key: 'tick_birth', direction: 'asc' };
    const columns = [['display_name', 'Agent Name'], ['model', 'Model Name'], ['tick_birth', 'Birth Tick'], ['tick_exit', 'Exit Tick'], ['description', 'Description']];
    const accessors = {
      tick_birth: agent => agent.tick_birth ?? agent.history.first_tick,
      tick_exit: agent => agent.tick_exit ?? agent.history.last_tick
    };
    const draw = () => {
      const term = search.value.trim().toLowerCase();
      const filtered = agents.filter(agent => [agent.display_name, agent.model, agent.lineage, agent.description].join(' ').toLowerCase().includes(term));
      const rows = sortedRecords(filtered, sort, accessors);
      results.innerHTML = `${mobileSortControls(columns, sort)}<div class="table-shell"><table class="data-table"><thead><tr>${sortableHeaders(columns, sort)}</tr></thead><tbody>${rows.map(agent => { const href = stationUrl(station.id, `agent/${encodeURIComponent(agent.key)}`); return `<tr data-href="${href}"><td data-label="Agent Name"><a href="${href}">${escapeHtml(agent.display_name)}</a></td><td data-label="Model Name">${escapeHtml(agent.model)}</td><td data-label="Birth Tick">${escapeHtml(agent.tick_birth ?? agent.history.first_tick ?? '—')}</td><td data-label="Exit Tick">${escapeHtml(agent.tick_exit ?? agent.history.last_tick ?? '—')}</td><td data-label="Description">${escapeHtml(agent.description || '—')}</td></tr>`; }).join('')}</tbody></table></div>${rows.length ? '' : '<div class="empty-state">No matching agents.</div>'}`;
    };
    bindSorting(results, sort, draw); bindRowLinks(results); search.addEventListener('input', draw); draw();
  }
  function messageText(entry) {
    if (Array.isArray(entry.parts)) return entry.parts.map(part => typeof part === 'string' ? part : part?.text ?? part?.content ?? '').filter(Boolean).join('\n\n');
    return entry.content || entry.text || '';
  }
  async function historyPage(path, signal) {
    const text = await fetchGzip(path, signal); const records = [];
    window.jsyaml.loadAll(text, value => { if (value && typeof value === 'object') records.push(value); });
    return records;
  }
  async function dialoguePageForTick(base, history, tick, signal) {
    const value = Number(tick);
    const hasRanges = history.pages.every(record => Number.isFinite(Number(record.first_tick)) && Number.isFinite(Number(record.last_tick)));
    if (hasRanges) return history.pages.findIndex(record => value >= Number(record.first_tick) && value <= Number(record.last_tick));
    let low = 0; let high = history.pages.length - 1;
    while (low <= high) {
      const middle = Math.floor((low + high) / 2); const record = history.pages[middle];
      const records = await historyPage(`${base}/dialogue/${record.file}`, signal);
      const ticks = records.map(entry => Number(entry.tick)).filter(Number.isFinite);
      const first = Math.min(...ticks); const last = Math.max(...ticks);
      if (ticks.some(entryTick => entryTick === value)) {
        let found = middle;
        while (found > 0) {
          const previous = history.pages[found - 1];
          const previousRecords = await historyPage(`${base}/dialogue/${previous.file}`, signal);
          if (!previousRecords.some(entry => String(entry.tick) === tick)) break;
          found -= 1;
        }
        return found;
      }
      if (!ticks.length || value < first) high = middle - 1;
      else if (value > last) low = middle + 1;
      else return -1;
    }
    return -1;
  }
  async function appendMessages(container, records, request, context) {
    const fragment = document.createDocumentFragment();
    for (let i = 0; i < records.length; i += 1) {
      current(request);
      const entry = records[i]; const stationRole = entry.role === 'user' || entry.role === 'system';
      const article = document.createElement('article'); article.className = `chat-bubble ${stationRole ? 'station' : 'agent'}`;
      const entryNumber = i + 1;
      article.dataset.dialoguePage = context.pageFile;
      article.dataset.dialogueEntry = String(entryNumber);
      article.dataset.dialogueTick = String(entry.tick ?? '');
      article.tabIndex = -1;
      const thinking = entry.thinking_content || entry.thinking_text || '';
      const rawMessage = messageText(entry);
      article.innerHTML = `<details class="dialogue-entry" open><summary class="chat-meta"><span>${stationRole ? 'Station' : 'Agent'}</span><span>Tick ${escapeHtml(entry.tick ?? '—')}</span><span class="dialogue-actions"><button class="copy-raw-dialogue" type="button">Copy raw</button><button class="copy-dialogue-link" type="button">Copy link</button></span><span class="collapse-label" aria-hidden="true"></span></summary><div class="chat-body">${thinking ? `<details class="thinking"${context.target?.thinkingOpen ? ' open' : ''}><summary>Thinking</summary><pre>${escapeHtml(String(thinking))}</pre></details>` : ''}${markdown(rawMessage)}</div></details>`;
      fragment.appendChild(article); enhance(article);
      article.querySelector('.copy-raw-dialogue').addEventListener('click', async event => {
        event.preventDefault(); event.stopPropagation(); const button = event.currentTarget;
        await copyText(rawMessage); button.textContent = 'Copied'; setTimeout(() => { button.textContent = 'Copy raw'; }, 1200);
      });
      const thinkingDetails = article.querySelector('.thinking');
      const linkButton = article.querySelector('.copy-dialogue-link');
      const updateLinkTitle = () => {
        linkButton.title = context.target?.thinkingOpen || thinkingDetails?.open ? 'Copy tick link with Thinking expanded' : 'Copy link to this tick';
      };
      thinkingDetails?.addEventListener('toggle', updateLinkTitle); updateLinkTitle();
      linkButton.addEventListener('click', async event => {
        event.preventDefault(); event.stopPropagation(); const button = event.currentTarget;
        const hash = dialogueTickUrl(context.stationId, context.agentKey, entry.tick, context.target?.thinkingOpen || Boolean(thinkingDetails?.open));
        await copyText(`${location.href.split('#')[0]}${hash}`); button.textContent = 'Copied'; setTimeout(() => { button.textContent = 'Copy link'; }, 1200);
      });
      if (i && i % 8 === 0) await new Promise(resolve => requestAnimationFrame(resolve));
    }
    if (context.prepend) container.prepend(fragment);
    else container.append(fragment);
  }
  async function renderAgent(station, key, target, signal, request) {
    const data = await fetchJSON(`data/${station.id}/agents/index.json`, signal); current(request);
    const agent = (data.agents || []).find(item => item.key === key); if (!agent) throw new Error('Agent not found');
    const base = `data/${station.id}/agents/${agent.key}`;
    const history = await fetchJSON(`${base}/dialogue/index.json`, signal); current(request);
    const targetPage = target ? await dialoguePageForTick(base, history, target.tick, signal) : 0;
    if (target && targetPage < 0) throw new Error(`Dialogue tick not found: ${target.tick}`);
    app.innerHTML = `${pageHeader(agent.display_name, '', `<a class="back-link" href="${stationUrl(station.id)}">Back to Agent Dialogue</a>`)}${meta([['Model', agent.model], ['Lineage', agent.lineage], ['Birth Tick', agent.tick_birth], ['Exit Tick', agent.tick_exit]])}<section class="dialogue-window" aria-labelledby="dialogue-title"><h2 id="dialogue-title" class="dialogue-window-title">Dialogue</h2><div id="load-previous-pager" class="pager dialogue-previous-pager" hidden><button id="load-previous" class="button" type="button">Load previous</button></div><div id="transcript" class="transcript"></div></section><div class="pager"><button id="load-more" class="button" type="button">Load more</button></div>`;
    const transcript = document.getElementById('transcript');
    const previousPager = document.getElementById('load-previous-pager');
    const previousButton = document.getElementById('load-previous');
    const nextButton = document.getElementById('load-more');
    let previousPage = target ? targetPage - 1 : -1;
    let nextPage = targetPage;
    let loadingPrevious = false; let loadingNext = false;
    let previousObserver = null; let nextObserver = null;
    const pageUrl = record => {
      const revision = record.sha256 ? `?v=${encodeURIComponent(record.sha256.slice(0, 16))}` : '';
      return `${base}/dialogue/${record.file}${revision}`;
    };
    const handleLoadError = (error, button, retryLabel) => {
      if (error.name === 'AbortError' || request !== state.request) return;
      button.disabled = false; button.hidden = false; button.textContent = retryLabel;
      button.title = error.message || 'The dialogue page could not be loaded.';
    };
    const updatePreviousButton = () => {
      const complete = previousPage < 0;
      if (complete) {
        previousObserver?.disconnect();
        previousPager.remove();
        return;
      }
      previousPager.hidden = false;
      previousButton.disabled = false;
      previousButton.textContent = `Load previous (${previousPage + 1} pages remaining)`;
    };
    const loadPrevious = async () => {
      if (loadingPrevious || previousPage < 0) return;
      loadingPrevious = true; previousButton.disabled = true; previousButton.textContent = 'Loading…'; previousButton.removeAttribute('title');
      try {
        const record = history.pages[previousPage];
        const records = await historyPage(pageUrl(record), signal);
        const anchor = transcript.firstElementChild;
        const anchorTop = anchor?.getBoundingClientRect().top;
        await appendMessages(transcript, records, request, { stationId: station.id, agentKey: agent.key, pageFile: record.file, target, prepend: true });
        previousPage -= 1;
        if (anchor && Number.isFinite(anchorTop)) window.scrollBy(0, anchor.getBoundingClientRect().top - anchorTop);
      } finally {
        loadingPrevious = false;
        if (request === state.request) updatePreviousButton();
      }
    };
    const loadNext = async () => {
      if (loadingNext || nextPage >= history.pages.length) return;
      loadingNext = true; nextButton.disabled = true; nextButton.textContent = 'Loading…'; nextButton.removeAttribute('title');
      try {
        const record = history.pages[nextPage];
        await appendMessages(transcript, await historyPage(pageUrl(record), signal), request, { stationId: station.id, agentKey: agent.key, pageFile: record.file, target });
        nextPage += 1;
      } finally {
        loadingNext = false;
        if (request === state.request) {
          const complete = nextPage >= history.pages.length;
          nextButton.disabled = false; nextButton.hidden = complete;
          nextButton.textContent = `Load more (${history.pages.length - nextPage} pages remaining)`;
          if (complete) nextObserver?.disconnect();
        }
      }
    };
    previousButton.addEventListener('click', () => loadPrevious().catch(error => handleLoadError(error, previousButton, 'Retry load previous')));
    nextButton.addEventListener('click', () => loadNext().catch(error => handleLoadError(error, nextButton, 'Retry load more')));
    updatePreviousButton();
    await loadNext();
    let focusedTarget = false;
    if (target) {
      current(request);
      const targetArticle = [...transcript.querySelectorAll('.chat-bubble')].find(article => article.dataset.dialogueTick === target.tick);
      if (!targetArticle) throw new Error(`Dialogue tick not found: ${target.tick}`);
      targetArticle.querySelector('.dialogue-entry').open = true;
      targetArticle.classList.add('dialogue-target');
      targetArticle.scrollIntoView({ block: 'start' });
      targetArticle.focus({ preventScroll: true });
      focusedTarget = true;
    }
    if (nextPage < history.pages.length && 'IntersectionObserver' in window) {
      nextObserver = new IntersectionObserver(entries => {
        if (entries.some(entry => entry.isIntersecting)) loadNext().catch(error => handleLoadError(error, nextButton, 'Retry load more'));
      }, { rootMargin: '600px 0px' });
      nextObserver.observe(nextButton);
    }
    if (previousPage >= 0 && 'IntersectionObserver' in window) {
      let previousArmed = false;
      let lastScrollY = window.scrollY;
      const previousIsNear = () => {
        const bounds = previousPager.getBoundingClientRect();
        return bounds.bottom >= -200 && bounds.top <= innerHeight + 200;
      };
      const maybeLoadPrevious = () => {
        if (previousArmed && previousIsNear()) loadPrevious().catch(error => handleLoadError(error, previousButton, 'Retry load previous'));
      };
      const handleScroll = () => {
        const scrollY = window.scrollY;
        if (scrollY < lastScrollY) previousArmed = true;
        lastScrollY = scrollY;
        maybeLoadPrevious();
      };
      previousObserver = new IntersectionObserver(entries => {
        if (entries.some(entry => entry.isIntersecting)) maybeLoadPrevious();
      }, { rootMargin: '200px 0px' });
      previousObserver.observe(previousPager);
      window.addEventListener('scroll', handleScroll, { passive: true });
      signal.addEventListener('abort', () => {
        window.removeEventListener('scroll', handleScroll);
        previousObserver?.disconnect(); nextObserver?.disconnect();
      }, { once: true });
    }
    return focusedTarget;
  }

  async function capsuleIndex(station, signal) { return fetchJSON(`data/${station.id}/capsules/index.json`, signal); }
  async function renderCapsules(station, type, signal, request) {
    const data = await capsuleIndex(station, signal); current(request);
    const records = (data.capsules || []).filter(item => item.type === type);
    const label = capsuleLabels[type] || type;
    const graphAction = type === 'archive' && records.some(item => !item.deleted) ? `<a class="button knowledge-graph-button" href="${stationUrl(station.id, 'archive-graph')}">Knowledge graph</a>` : '';
    app.innerHTML = `${pageHeader(label)}<div class="toolbar"><label class="sr-only" for="search">Search</label><input id="search" type="search" placeholder="Search ${escapeHtml(label.toLowerCase())}">${graphAction}</div><div id="results"></div>`;
    const search = document.getElementById('search'); const results = document.getElementById('results'); let shown = 100;
    const sort = { key: 'created_tick', direction: 'asc' };
    const columns = type === 'archive'
      ? [['title', 'Title'], ['id', 'ID'], ['author', 'Author'], ['created_tick', 'Accepted'], ['reviewer_score', 'Review Score'], ['word_count', 'Words']]
      : type === 'question'
        ? [['title', 'Title'], ['id', 'ID'], ['author', 'Author'], ['created_tick', 'Authored'], ['question_status', 'Status'], ['question_net_upvote', 'Net Upvote'], ['reply_count', 'Replies']]
        : type === 'mail'
          ? [['title', 'Title'], ['id', 'ID'], ['author', 'Author'], ['recipients', 'Recipients'], ['created_tick', 'Created'], ['updated_tick', 'Updated'], ['reply_count', 'Replies']]
          : [['title', 'Title'], ['id', 'ID'], ['author', 'Author'], ['created_tick', 'Created'], ['updated_tick', 'Updated'], ['reply_count', 'Replies'], ['word_count', 'Words']];
    const accessors = { id: item => capsuleDisplayId(item.id) };
    const cell = (item, key) => {
      if (key === 'title') return `<a href="${stationUrl(station.id, `capsule/${type}/${encodeURIComponent(item.key)}`)}">${escapeHtml(item.title)}</a>`;
      if (key === 'id') return escapeHtml(capsuleDisplayId(item.id));
      if (key === 'reviewer_score') return `<span class="review-score">${escapeHtml(reviewScore(item.reviewer_score))}</span>`;
      if (key === 'question_status') return statusBadge(item.question_status);
      if (key === 'recipients') return escapeHtml((item.recipients || []).join(', ') || '—');
      return escapeHtml(item[key] ?? '—');
    };
    const draw = () => {
      const term = search.value.trim().toLowerCase();
      const filtered = records.filter(item => [item.id, item.title, item.author, ...(item.recipients || []), ...(item.tags || [])].join(' ').toLowerCase().includes(term));
      const ordered = sortedRecords(filtered, sort, accessors); const visible = ordered.slice(0, shown);
      results.innerHTML = `${mobileSortControls(columns, sort)}<div class="table-shell"><table class="data-table capsule-table capsule-table-${type}"><thead><tr>${sortableHeaders(columns, sort)}</tr></thead><tbody>${visible.map(item => { const href = stationUrl(station.id, `capsule/${type}/${encodeURIComponent(item.key)}`); return `<tr data-href="${href}">${columns.map(([key, heading]) => `<td data-label="${escapeHtml(heading)}">${cell(item, key)}</td>`).join('')}</tr>`; }).join('')}</tbody></table></div>${visible.length < ordered.length ? `<div class="pager"><button id="more-records" class="button" type="button">Load more</button></div>` : ''}${ordered.length ? '' : '<div class="empty-state">No matching records.</div>'}`;
      document.getElementById('more-records')?.addEventListener('click', () => { shown += 100; draw(); });
    };
    bindSorting(results, sort, () => { shown = 100; draw(); }); bindRowLinks(results); search.addEventListener('input', () => { shown = 100; draw(); }); draw();
  }
  async function renderArchiveGraph(station, signal, request) {
    if (!window.StationArchiveGraph) throw new Error('Archive knowledge graph is unavailable');
    const data = await capsuleIndex(station, signal); current(request);
    const records = (data.capsules || []).filter(item => item.type === 'archive' && !item.deleted);
    app.innerHTML = `<section class="archive-graph-page">${pageHeader('Archive knowledge graph', 'Explicit citations between Archive papers', `<a class="back-link" href="${stationUrl(station.id, 'archive')}">Back to Archive Paper</a>`)}<div class="archive-graph-toolbar"><label class="archive-graph-search-wrap"><span class="sr-only">Find a paper</span><input class="archive-graph-search" type="search" list="archive-graph-suggestions" placeholder="Find a paper or author"><datalist id="archive-graph-suggestions" class="archive-graph-suggestions"></datalist></label><div class="archive-graph-controls" aria-label="Graph controls"><button class="button" type="button" data-graph-action="out" aria-label="Zoom out">−</button><button class="button" type="button" data-graph-action="in" aria-label="Zoom in">+</button><button class="button" type="button" data-graph-action="fit">Fit</button><button class="button archive-graph-theme" type="button">Theme</button></div><span class="archive-graph-status" aria-live="polite"></span></div><div class="archive-graph-shell"><canvas class="archive-graph-canvas" tabindex="0" aria-label="Interactive Archive citation graph"></canvas><div class="archive-graph-tooltip" hidden></div><div class="archive-graph-legend" aria-hidden="true"><span class="archive-graph-tick-key">Published tick <em>Earlier</em><i class="tick-gradient"></i><em>Later</em></span><span><i class="spotlight-ring"></i> Spotlight source</span><span><i class="citation-line citation-outgoing"></i> Cites</span><span><i class="citation-line citation-incoming"></i> Cited by</span><span>Larger nodes = more citations received</span></div></div><p class="archive-graph-help"><span>Drag to move · Scroll or use +/− to zoom</span></p></section>`;
    document.body.classList.add('archive-graph-active');
    state.graphCleanup = window.StationArchiveGraph.mount({
      root: app,
      records,
      hrefFor: record => stationUrl(station.id, `capsule/archive/${encodeURIComponent(record.key)}`)
    });
    app.querySelector('.archive-graph-theme').addEventListener('click', () => themeToggle.click());
  }
  async function renderCapsule(station, type, key, signal, request) {
    const data = await capsuleIndex(station, signal); current(request);
    const record = (data.capsules || []).find(item => item.type === type && item.key === key); if (!record) throw new Error('Record not found');
    const raw = await fetchGzip(`data/${station.id}/${record.file}`, signal); current(request);
    const capsule = window.jsyaml.load(raw) || {};
    const messages = (Array.isArray(capsule.messages) ? capsule.messages : []).filter(message => !message?.is_deleted);
    const back = stationUrl(station.id, type === 'public' || type === 'private' ? `memory/${type}` : type);
    const metadata = [['Author', record.author], [type === 'archive' ? 'Accepted' : type === 'question' ? 'Authored' : 'Created', record.created_tick], ['Updated', record.updated_tick], ['ID', capsuleDisplayId(record.id)]];
    if (type === 'archive') metadata.splice(3, 0, ['Review Score', reviewScore(record.reviewer_score)]);
    if (['public', 'private', 'mail'].includes(type)) metadata.splice(3, 0, ['Replies', record.reply_count]);
    if (type === 'mail') metadata.splice(1, 0, ['Recipients', (record.recipients || []).join(', ') || '—']);
    if (type === 'question') metadata.splice(3, 0, ['Status', record.question_status], ['Net Upvote', record.question_net_upvote], ['Replies', record.reply_count]);
    const solvedBy = String(capsule.question_solved_by_message_id || record.question_solved_by_message_id || '');
    const messageCards = messages.map((message, index) => {
      const isQuestion = type === 'question' && index === 0;
      const accepted = type === 'question' && solvedBy && String(message.message_id || '') === solvedBy;
      const kind = isQuestion ? 'Question' : type === 'question' ? `Reply ${index}` : `Message ${index + 1}`;
      const action = isQuestion ? 'posted the question' : type === 'question' ? 'posted a reply' : 'posted a message';
      const vote = type === 'question' ? (isQuestion ? `Net upvote: ${record.question_net_upvote ?? 0}` : `Solution net upvote: ${message.solution_net_upvote ?? 0}`) : '';
      return `<section class="capsule-message${accepted ? ' is-accepted' : ''}"><header class="capsule-message-header"><div class="capsule-message-byline"><strong>${escapeHtml(message.author_name || record.author)}</strong><span>${action} at Tick ${escapeHtml(message.posted_at_tick ?? '—')}</span>${accepted ? '<span class="accepted-solution">Accepted Solution</span>' : ''}</div><div class="capsule-message-details"><span class="message-kind">${escapeHtml(kind)}</span>${message.title ? `<span>${escapeHtml(message.title)}</span>` : ''}${message.message_id ? `<span>${escapeHtml(message.message_id)}</span>` : ''}${vote ? `<span>${escapeHtml(vote)}</span>` : ''}</div></header>${markdown(message.content || '')}</section>`;
    }).join('');
    const missingSolution = type === 'question' && record.question_status === 'solved' && solvedBy && !messages.some(message => String(message.message_id || '') === solvedBy)
      ? '<div class="capsule-thread-note">The accepted solution is no longer available in the active thread.</div>' : '';
    app.innerHTML = `${pageHeader(record.title, '', `<a class="back-link" href="${back}">Back to ${escapeHtml(capsuleLabels[type] || type)}</a>`)}${meta(metadata)}<div class="tag-list">${(record.tags || []).map(tag => `<span class="tag">${escapeHtml(tag)}</span>`).join('')}</div><article class="record-paper capsule-thread">${capsule.abstract ? `<section class="capsule-message capsule-abstract"><p class="record-label">Abstract</p>${markdown(capsule.abstract)}</section>` : ''}${missingSolution}${messageCards || `<section class="capsule-message">${markdown(capsule.content || raw)}</section>`}</article>`;
    enhance();
  }

  async function renderEvaluations(station, signal, request) {
    const data = await fetchJSON(`data/${station.id}/evaluations/index.json`, signal); current(request);
    const records = data.evaluations || [];
    app.innerHTML = `${pageHeader('Research Submission')}<div class="toolbar"><label class="sr-only" for="search">Search submissions</label><input id="search" type="search" placeholder="Search submissions"></div><div id="results"></div>`;
    const search = document.getElementById('search'); const results = document.getElementById('results'); let shown = 100;
    const sort = { key: 'id', direction: 'asc' };
    const columns = [['title', 'Title'], ['id', 'ID'], ['author', 'Author'], ['submitted_tick', 'Submitted Tick'], ['score', 'Score'], ['status', 'Status']];
    const draw = () => {
      const term = search.value.trim().toLowerCase(); const filtered = records.filter(item => [item.id, item.title, item.author, item.status, ...(item.tags || [])].join(' ').toLowerCase().includes(term)); const ordered = sortedRecords(filtered, sort); const visible = ordered.slice(0, shown);
      results.innerHTML = `${mobileSortControls(columns, sort)}<div class="table-shell"><table class="data-table"><thead><tr>${sortableHeaders(columns, sort)}</tr></thead><tbody>${visible.map(item => { const href = stationUrl(station.id, `evaluation/${encodeURIComponent(item.key)}`); return `<tr data-href="${href}"><td data-label="Title"><a href="${href}">${escapeHtml(item.title)}</a></td><td data-label="ID">${escapeHtml(item.id)}</td><td data-label="Author">${escapeHtml(item.author)}</td><td data-label="Submitted Tick">${escapeHtml(item.submitted_tick ?? '—')}</td><td data-label="Score">${escapeHtml(item.score ?? 'n.a.')}</td><td data-label="Status">${escapeHtml(item.status)}</td></tr>`; }).join('')}</tbody></table></div>${visible.length < ordered.length ? '<div class="pager"><button id="more-records" class="button" type="button">Load more</button></div>' : ''}${ordered.length ? '' : '<div class="empty-state">No matching submissions.</div>'}`;
      document.getElementById('more-records')?.addEventListener('click', () => { shown += 100; draw(); });
    };
    bindSorting(results, sort, () => { shown = 100; draw(); }); bindRowLinks(results); search.addEventListener('input', () => { shown = 100; draw(); }); draw();
  }
  async function renderEvaluation(station, key, signal, request) {
    const data = await fetchJSON(`data/${station.id}/evaluations/index.json`, signal); current(request);
    const record = (data.evaluations || []).find(item => item.key === key); if (!record) throw new Error('Research submission not found');
    const raw = await fetchGzip(`data/${station.id}/${record.file}`, signal); current(request); const item = window.jsyaml.load(raw) || {};
    app.innerHTML = `${pageHeader(record.title, '', `<a class="back-link" href="${stationUrl(station.id, 'evaluations')}">Back to Research Submission</a>`)}${meta([['Author', record.author], ['Submitted Tick', record.submitted_tick], ['Score', record.score], ['Status', record.status], ['ID', record.id]])}<article class="record-paper">${record.abstract ? `<section class="record-section"><p class="record-label">Abstract</p>${markdown(record.abstract)}</section>` : ''}${item.instruction ? `<section class="record-section"><p class="record-label">Instruction</p>${markdown(item.instruction)}</section>` : ''}${item.result ? `<section class="record-section"><p class="record-label">Result</p>${markdown(item.result)}</section>` : ''}</article>`;
    enhance();
  }

  function renderNotebooks() {
    showNavbar(null);
    const packages = state.catalog.artifacts
      .filter(artifact => !artifact.hidden)
      .sort((left, right) => naturalOrder.compare(left.title, right.title));
    app.innerHTML = `<div class="notebook-list">${pageHeader('Verification notebooks', '', '<a class="back-link" href="#/">Back to station viewer</a>')}${packages.map(artifact => `<section class="notebook-group"><h2>${escapeHtml(artifact.title)}</h2><ul>${artifact.notebooks.map(path => `<li><a href="${notebookUrl(artifact.id, path)}">${escapeHtml(path)}</a></li>`).join('')}</ul><p><a href="${githubTree(`artifacts/${artifact.id}`)}" target="_blank" rel="noopener noreferrer">Supporting files</a> · <a href="${bundleFile(artifact.id)}" download>Download verification bundle</a></p></section>`).join('')}</div>`;
  }

  async function renderNotebook(artifactId, path, section, signal, request) {
    showNavbar(null);
    const artifact = state.catalog.artifacts.find(item => item.id === artifactId && !item.hidden);
    if (!artifact || !artifact.notebooks.includes(path)) throw new Error('Verification notebook not found');
    if (!window.StationNotebookRenderer) throw new Error('Notebook renderer is unavailable');
    const notebook = await fetchJSON(`artifacts/${artifact.id}/${path}`, signal); current(request);
    const actions = `<div class="button-row notebook-actions"><a class="back-link" href="#/">Back to station viewer</a><a class="button" href="${githubFile(`artifacts/${artifact.id}/${path}`)}" target="_blank" rel="noopener noreferrer">View source on GitHub</a><a class="button" href="${bundleFile(artifact.id)}" download>Download verification bundle</a></div>`;
    app.innerHTML = `<article class="notebook-page">${pageHeader(artifact.title, path, actions)}<div id="notebook-host" class="notebook-host" aria-label="${escapeHtml(artifact.title)} verification notebook"></div></article>`;
    const mounted = await window.StationNotebookRenderer.render(document.getElementById('notebook-host'), notebook); current(request);
    state.notebookCleanup = () => mounted.dispose();
    if (section) {
      const found = await mounted.scrollTo(section); current(request);
      if (!found) throw new Error(`Notebook section not found: ${section}`);
    }
  }

  function showError(error) {
    console.error(error); app.innerHTML = `<div class="error-state"><h1>Could not load this page</h1><p>${escapeHtml(error?.message || error)}</p><p><a href="#/">Back to Stations</a></p></div>`;
  }
  function routeState() {
    const value = location.hash.replace(/^#\/?/, '');
    const marker = value.indexOf('?');
    const path = marker < 0 ? value : value.slice(0, marker);
    const query = new URLSearchParams(marker < 0 ? '' : value.slice(marker + 1));
    return { parts: path ? path.split('/').filter(Boolean).map(part => decodeURIComponent(part)) : [], query };
  }
  async function route() {
    state.controller?.abort(); state.graphCleanup?.(); state.graphCleanup = null; state.notebookCleanup?.(); state.notebookCleanup = null; document.body.classList.remove('archive-graph-active');
    const controller = new AbortController(); state.controller = controller; const request = ++state.request;
    closeMenu(); app.innerHTML = '<div class="loading-state">Loading…</div>'; window.scrollTo(0, 0);
    try {
      let focusedTarget = false;
      const { parts, query } = routeState();
      if (!parts.length) { renderDashboard(); return; }
      if (parts[0] === 'notebooks' && parts.length === 1) { renderNotebooks(); return; }
      if (parts[0] === 'notebooks') { await renderNotebook(parts[1], parts[2], parts[3] || '', controller.signal, request); return; }
      const station = stationById(parts[0]); if (!station) throw new Error('Station not found');
      const page = parts[1] || 'agents'; const active = page === 'memory' ? parts[2] : page === 'capsule' ? parts[2] : page === 'agent' ? 'agents' : page === 'evaluation' ? 'evaluations' : page === 'archive-graph' ? 'archive' : page;
      showNavbar(station, active);
      if (page === 'agents') await renderAgents(station, controller.signal, request);
      else if (page === 'agent' && parts.length === 3) focusedTarget = await renderAgent(station, parts[2], parseDialogueTarget(query), controller.signal, request);
      else if (page === 'memory') await renderCapsules(station, parts[2], controller.signal, request);
      else if (['archive', 'mail', 'question'].includes(page)) await renderCapsules(station, page, controller.signal, request);
      else if (page === 'archive-graph') await renderArchiveGraph(station, controller.signal, request);
      else if (page === 'capsule') await renderCapsule(station, parts[2], parts[3], controller.signal, request);
      else if (page === 'evaluations') await renderEvaluations(station, controller.signal, request);
      else if (page === 'evaluation') await renderEvaluation(station, parts[2], controller.signal, request);
      else throw new Error('Page not found');
      current(request); if (!focusedTarget) app.focus({ preventScroll: true });
    } catch (error) { if (error.name !== 'AbortError' && request === state.request) showError(error); }
  }
  async function init() {
    configureMarkdown();
    setTheme(localStorage.getItem('station-viewer-theme') || 'light');
    themeToggle.addEventListener('click', () => setTheme(document.documentElement.dataset.theme === 'light' ? 'dark' : 'light'));
    mobileToggle.addEventListener('click', () => { const open = !navLinks.classList.contains('open'); navLinks.classList.toggle('open', open); backdrop.classList.toggle('open', open); mobileToggle.setAttribute('aria-expanded', String(open)); mobileToggle.setAttribute('aria-label', open ? 'Close navigation menu' : 'Open navigation menu'); });
    navLinks.addEventListener('click', event => { if (event.target.closest('a')) closeMenu(); });
    backdrop.addEventListener('click', closeMenu); document.addEventListener('keydown', event => { if (event.key === 'Escape') closeMenu(); });
    state.catalog = await fetchJSON('catalog.json');
    stationSelector.innerHTML = state.catalog.stations.map(station => `<option value="${escapeHtml(station.id)}">${escapeHtml(station.title)}</option>`).join('');
    stationSelector.addEventListener('change', () => { location.hash = stationUrl(stationSelector.value).slice(1); });
    window.addEventListener('hashchange', route); await route();
  }
  init().catch(showError);
})();
