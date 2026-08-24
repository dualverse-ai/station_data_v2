#!/usr/bin/env node
/* Capture an exact emulated viewport from an already-running local Chrome CDP. */

import fs from 'node:fs/promises';

const [url, output, widthText = '390', heightText = '844'] = process.argv.slice(2);
if (!url || !output) throw new Error('usage: browser_qc.mjs URL OUTPUT [WIDTH HEIGHT]');
const width = Number(widthText);
const height = Number(heightText);
const target = await fetch(`http://127.0.0.1:9222/json/new?${encodeURIComponent(url)}`, { method: 'PUT' }).then(response => response.json());
const socket = new WebSocket(target.webSocketDebuggerUrl);
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

await send('Page.enable');
await send('Runtime.enable');
await send('Emulation.setDeviceMetricsOverride', {
  width, height, deviceScaleFactor: 1, mobile: true,
  screenWidth: width, screenHeight: height,
});
await send('Page.navigate', { url });
await new Promise(resolve => setTimeout(resolve, 6000));
const metrics = await send('Runtime.evaluate', {
  returnByValue: true,
  expression: `(() => {
    const overflow = [...document.querySelectorAll('body *')].filter(node => {
      const rect = node.getBoundingClientRect();
      return rect.width > 0 && (rect.right > innerWidth + 1 || rect.left < -1);
    }).slice(0, 20).map(node => ({tag: node.tagName, className: String(node.className), rect: node.getBoundingClientRect().toJSON()}));
    const rect = selector => document.querySelector(selector)?.getBoundingClientRect().toJSON();
    const logo = document.querySelector('.nav-logo, .dashboard-logo');
    const bubble = document.querySelector('.chat-bubble');
    const sheets = [...document.styleSheets].map(sheet => ({href: sheet.href, bubbleRules: (() => { try { return [...sheet.cssRules].filter(rule => rule.cssText.includes('.chat-bubble')).map(rule => rule.cssText); } catch { return []; } })()}));
    return {innerWidth, innerHeight, devicePixelRatio, scrollX, scrollY, documentWidth: document.documentElement.scrollWidth, bodyWidth: document.body.scrollWidth, viewport: document.querySelector('meta[name="viewport"]')?.content, app: rect('#app'), transcript: rect('.transcript'), bubble: bubble ? {...bubble.getBoundingClientRect().toJSON(), width: getComputedStyle(bubble).width, maxWidth: getComputedStyle(bubble).maxWidth} : null, sheets, logo: {...(logo?.getBoundingClientRect().toJSON() || {}), naturalWidth: logo?.naturalWidth, complete: logo?.complete}, menu: rect('.mobile-menu-toggle'), overflow};
  })()`
});
const screenshot = await send('Page.captureScreenshot', { format: 'png', fromSurface: true });
await fs.writeFile(output, Buffer.from(screenshot.data, 'base64'));
console.log(JSON.stringify(metrics.result.value, null, 2));
socket.close();
