#!/usr/bin/env node
/* Verify compact tick dialogue links against an already-running local Chrome CDP. */

import assert from 'node:assert/strict';

const [baseArg = 'http://127.0.0.1:8765/', cdpRoot = 'http://127.0.0.1:9222'] = process.argv.slice(2);
const baseUrl = new URL(baseArg);
const ordinaryHash = '#/uncertainty/agent/Nova-II-732a9eba9a';
const earlyHash = `${ordinaryHash}?tick=794`;
const collapsedHash = `${ordinaryHash}?tick=838`;
const thinkingHash = `${collapsedHash}&thinking=open`;
const missingHash = `${ordinaryHash}?tick=999999999`;
const urlFor = hash => { const url = new URL(baseUrl); url.hash = hash; return url.href; };

const browserTarget = await fetch(`${cdpRoot}/json/new?${encodeURIComponent('about:blank')}`, { method: 'PUT' }).then(response => {
  if (!response.ok) throw new Error(`Chrome CDP returned ${response.status}`);
  return response.json();
});
const socket = new WebSocket(browserTarget.webSocketDebuggerUrl);
await new Promise((resolve, reject) => {
  socket.addEventListener('open', resolve, { once: true });
  socket.addEventListener('error', reject, { once: true });
});

let sequence = 0;
const pending = new Map();
socket.addEventListener('message', event => {
  const message = JSON.parse(event.data);
  if (!message.id || !pending.has(message.id)) return;
  const { resolve, reject } = pending.get(message.id);
  pending.delete(message.id);
  if (message.error) reject(new Error(message.error.message));
  else resolve(message.result || {});
});
const send = (method, params = {}) => new Promise((resolve, reject) => {
  const id = ++sequence;
  pending.set(id, { resolve, reject });
  socket.send(JSON.stringify({ id, method, params }));
});
const evaluate = async expression => {
  const result = await send('Runtime.evaluate', { expression, awaitPromise: true, returnByValue: true });
  if (result.exceptionDetails) throw new Error(result.exceptionDetails.exception?.description || result.exceptionDetails.text);
  return result.result?.value;
};
const waitFor = async (expression, label, timeoutMs = 30000) => {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    if (await evaluate(expression)) return;
    await new Promise(resolve => setTimeout(resolve, 100));
  }
  const diagnostic = await evaluate(`(() => {
    const target = document.querySelector('.dialogue-target');
    return {
      hash: location.hash,
      error: document.querySelector('.error-state')?.textContent,
      pages: [...new Set([...document.querySelectorAll('.chat-bubble')].map(node => node.dataset.dialoguePage))],
      targetTick: target?.dataset.dialogueTick,
      targetEntry: target?.dataset.dialogueEntry,
      targetTop: target?.getBoundingClientRect().top,
      targetFocused: document.activeElement === target,
      thinkingCount: document.querySelectorAll('.thinking').length,
      openThinkingCount: document.querySelectorAll('.thinking[open]').length
    };
  })()`);
  throw new Error(`Timed out waiting for ${label}: ${JSON.stringify(diagnostic)}`);
};
const waitForOrdinary = () => waitFor(
  `location.hash === ${JSON.stringify(ordinaryHash)}
    && document.querySelector('.transcript .chat-bubble')?.dataset.dialoguePage === 'page-0001.yamll.gz'
    && !document.querySelector('.dialogue-target')`,
  'ordinary page-one route',
  60000
);
const tickReadyExpression = (hash, thinkingOpen) => `(() => {
  const target = document.querySelector('.dialogue-target');
  const thinking = [...document.querySelectorAll('.thinking')];
  return location.hash === ${JSON.stringify(hash)}
    && document.querySelector('.transcript .chat-bubble')?.dataset.dialoguePage === 'page-0009.yamll.gz'
    && target?.dataset.dialogueEntry === '1'
    && target?.dataset.dialogueTick === '838'
    && document.activeElement === target
    && target.getBoundingClientRect().top >= 60
    && target.getBoundingClientRect().top < 180
    && !document.querySelector('[data-dialogue-page="page-0008.yamll.gz"]')
    && thinking.every(details => details.open === ${thinkingOpen});
})()`;
const waitForTick = (hash, thinkingOpen) => waitFor(tickReadyExpression(hash, thinkingOpen), thinkingOpen ? 'global Thinking tick route' : 'collapsed tick route');
const copyTargetLink = async expectedHash => {
  await evaluate(`(() => {
    Object.defineProperty(navigator, 'clipboard', {
      configurable: true,
      value: { writeText: async value => { window.__copiedDialogueLink = value; } }
    });
    window.__copiedDialogueLink = '';
    document.querySelector('.dialogue-target .copy-dialogue-link').click();
  })()`);
  await waitFor(`window.__copiedDialogueLink === ${JSON.stringify(urlFor(expectedHash))}`, 'compact copied link');
};
const copyLoadedEntryLink = async (selector, thinkingOpen) => {
  const tick = await evaluate(`(() => {
    const entry = document.querySelector(${JSON.stringify(selector)});
    window.__copiedDialogueLink = '';
    entry.querySelector('.copy-dialogue-link').click();
    return entry.dataset.dialogueTick;
  })()`);
  const expectedHash = `${ordinaryHash}?tick=${encodeURIComponent(tick)}${thinkingOpen ? '&thinking=open' : ''}`;
  await waitFor(`window.__copiedDialogueLink === ${JSON.stringify(urlFor(expectedHash))}`, 'loaded entry copied link');
  return tick;
};
const elapsedTransition = async (hash, ready) => {
  const started = performance.now();
  await evaluate(`location.hash = ${JSON.stringify(hash)}`);
  await ready();
  return Math.round(performance.now() - started);
};

try {
  await send('Page.enable');
  await send('Runtime.enable');
  await send('Network.enable');
  await send('Network.setCacheDisabled', { cacheDisabled: true });

  await send('Page.navigate', { url: urlFor(ordinaryHash) });
  await waitForOrdinary();
  assert.equal(await evaluate("document.querySelectorAll('.copy-dialogue-link').length > 0"), true, 'copy-link control should render');
  assert.equal(await evaluate("Boolean(document.getElementById('load-previous-pager'))"), false, 'ordinary page-one route should not retain exhausted previous-page UI');

  await evaluate(`location.hash = ${JSON.stringify(earlyHash)}`);
  await waitFor(`location.hash === ${JSON.stringify(earlyHash)}
    && document.querySelector('.transcript .chat-bubble')?.dataset.dialoguePage === 'page-0002.yamll.gz'
    && document.querySelector('.dialogue-target')?.dataset.dialogueTick === '794'
    && Boolean(document.getElementById('load-previous-pager'))`, 'early compact tick route');
  await evaluate('window.scrollBy(0, -1)');
  await waitFor(`Boolean(document.querySelector('[data-dialogue-page="page-0001.yamll.gz"]'))
    && !document.getElementById('load-previous-pager')`, 'exhausted previous-page UI removal');

  const collapsedMs = await elapsedTransition(collapsedHash, () => waitForTick(collapsedHash, false));
  await copyTargetLink(collapsedHash);

  const thinkingMs = await elapsedTransition(thinkingHash, () => waitForTick(thinkingHash, true));
  await copyTargetLink(thinkingHash);
  const initialThinkingCount = await evaluate("document.querySelectorAll('.thinking').length");

  await new Promise(resolve => setTimeout(resolve, 300));
  assert.equal(await evaluate("Boolean(document.querySelector('[data-dialogue-page=\"page-0008.yamll.gz\"]'))"), false, 'previous page should not load before upward scrolling');
  await evaluate(`(() => {
    const target = document.querySelector('.dialogue-target');
    window.scrollBy(0, -1);
    window.__dialogueAnchorTop = target.getBoundingClientRect().top;
  })()`);
  await waitFor(`Boolean(document.querySelector('[data-dialogue-page="page-0008.yamll.gz"]'))`, 'automatic previous-page load');
  assert.equal(await evaluate(`Math.abs(document.querySelector('.dialogue-target').getBoundingClientRect().top - window.__dialogueAnchorTop) < 2`), true, 'prepending should preserve the viewport anchor');
  assert.equal(await evaluate(`(() => {
    const previous = [...document.querySelectorAll('[data-dialogue-page="page-0008.yamll.gz"] .thinking')];
    return previous.length > 0 && previous.every(details => details.open);
  })()`), true, 'previous-page Thinking panels should be expanded');
  const copiedPreviousTick = await copyLoadedEntryLink('[data-dialogue-page="page-0008.yamll.gz"]', true);
  assert.notEqual(copiedPreviousTick, '838', 'a previous entry should copy its own tick');

  await evaluate("document.getElementById('load-more').click()");
  await waitFor(`Boolean(document.querySelector('[data-dialogue-page="page-0010.yamll.gz"]'))`, 'first future dialogue page');
  await evaluate("document.getElementById('load-more').click()");
  await waitFor(`(() => {
    const later = [...document.querySelectorAll('[data-dialogue-page="page-0011.yamll.gz"] .thinking')];
    return later.length > 0 && [...document.querySelectorAll('.thinking')].every(details => details.open);
  })()`, 'future page Thinking expansion');

  await send('Page.reload');
  await waitForTick(thinkingHash, true);
  await evaluate('history.back()');
  await waitForTick(collapsedHash, false);
  await evaluate('history.forward()');
  await waitForTick(thinkingHash, true);

  const missingStarted = performance.now();
  await evaluate(`location.hash = ${JSON.stringify(missingHash)}`);
  await waitFor(`location.hash === ${JSON.stringify(missingHash)}
    && document.querySelector('.error-state')?.textContent.includes('Dialogue tick not found: 999999999')`, 'visible missing-tick error');
  const missingMs = Math.round(performance.now() - missingStarted);
  await evaluate('history.back()');
  await waitForTick(thinkingHash, true);

  const state = await evaluate(`(() => ({
    hash: location.hash,
    targetEntry: document.querySelector('.dialogue-target')?.dataset.dialogueEntry,
    targetTick: document.querySelector('.dialogue-target')?.dataset.dialogueTick,
    renderedPages: [...new Set([...document.querySelectorAll('.chat-bubble')].map(node => node.dataset.dialoguePage))],
    thinkingCount: document.querySelectorAll('.thinking').length,
    openThinkingCount: document.querySelectorAll('.thinking[open]').length,
    focused: document.activeElement === document.querySelector('.dialogue-target')
  }))()`);
  console.log(JSON.stringify({
    ok: true,
    checks: ['ordinary-page-one', 'zero-remaining-previous-ui-absent', 'exhausted-previous-ui-removed', 'compact-tick-direct-load', 'first-entry-at-tick', 'collapsed-default', 'global-thinking-expanded', 'no-eager-previous-load', 'automatic-previous-page', 'viewport-anchor-preserved', 'previous-page-thinking-expanded', 'future-page-thinking-expanded', 'per-entry-copy-link', 'refresh', 'back-forward', 'visible-missing-tick'],
    timingsMs: { collapsed: collapsedMs, thinking: thinkingMs, missing: missingMs },
    initialThinkingCount,
    copiedPreviousTick,
    state
  }, null, 2));
} finally {
  socket.close();
  await fetch(`${cdpRoot}/json/close/${encodeURIComponent(browserTarget.id)}`).catch(() => {});
}
