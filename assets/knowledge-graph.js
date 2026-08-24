/* Isolated beta: interactive citation graph for Archive papers. */
(() => {
  'use strict';

  const clamp = (value, low, high) => Math.max(low, Math.min(high, value));
  const hash = value => {
    let result = 2166136261;
    for (const char of String(value || 'Unknown')) result = Math.imul(result ^ char.charCodeAt(0), 16777619);
    return result >>> 0;
  };
  const archiveNumber = value => String(value || '').match(/_(\d+)$/)?.[1] || value;
  const mix = (from, to, amount) => `rgb(${from.map((value, index) => Math.round(value + (to[index] - value) * amount)).join(' ')})`;
  const tickColor = amount => amount < .5 ? mix([49, 95, 168], [31, 150, 120], amount * 2) : mix([31, 150, 120], [217, 119, 50], (amount - .5) * 2);

  function prepare(records) {
    const ticks = records.map(record => Number(record.created_tick)).filter(Number.isFinite);
    const firstTick = Math.min(...ticks, 0); const lastTick = Math.max(...ticks, firstTick + 1);
    const nodes = records.map((record, index) => ({
      record, index, id: String(record.id).toLowerCase(),
      spotlight: record.spotlight === true,
      x: 0, y: 0, vx: 0, vy: 0, incoming: 0, outgoing: 0, radius: 5,
      color: tickColor(Number.isFinite(Number(record.created_tick)) ? (Number(record.created_tick) - firstTick) / Math.max(1, lastTick - firstTick) : .5)
    }));
    const byId = new Map(nodes.map(node => [node.id, node]));
    const edges = [];
    nodes.forEach(source => {
      const seen = new Set();
      (source.record.citations || []).forEach(rawTarget => {
        const target = byId.get(String(rawTarget).toLowerCase());
        if (!target || target === source || seen.has(target.id)) return;
        seen.add(target.id); source.outgoing += 1; target.incoming += 1;
        edges.push({ source, target });
      });
    });
    nodes.forEach(node => { node.radius = clamp(4.5 + Math.sqrt(node.incoming) * 1.7, 4.5, 13); });
    return { nodes, edges };
  }

  function layout(nodes, edges) {
    if (!nodes.length) return;
    const ticks = nodes.map(node => Number(node.record.created_tick)).filter(Number.isFinite);
    const lowTick = Math.min(...ticks, 0); const highTick = Math.max(...ticks, lowTick + 1);
    const width = Math.max(1500, Math.sqrt(nodes.length) * 125); const height = Math.max(900, Math.sqrt(nodes.length) * 75);
    nodes.forEach((node, index) => {
      const tick = Number(node.record.created_tick);
      const ratio = Number.isFinite(tick) ? (tick - lowTick) / Math.max(1, highTick - lowTick) : index / Math.max(1, nodes.length - 1);
      node.targetX = 100 + ratio * (width - 200);
      node.x = node.targetX + ((hash(node.id) % 101) - 50);
      node.y = 80 + (hash(`${node.id}:y`) % 10000) / 10000 * (height - 160);
    });
    for (let step = 0; step < 155; step += 1) {
      const cooling = 1 - step / 190;
      for (let left = 0; left < nodes.length; left += 1) {
        for (let right = left + 1; right < nodes.length; right += 1) {
          const a = nodes[left]; const b = nodes[right];
          let dx = b.x - a.x; let dy = b.y - a.y;
          let distanceSquared = dx * dx + dy * dy;
          if (distanceSquared > 52000) continue;
          if (distanceSquared < 4) { dx = 2; dy = 1; distanceSquared = 5; }
          const force = Math.min(3.1, 1150 / distanceSquared) * cooling;
          const distance = Math.sqrt(distanceSquared);
          const fx = dx / distance * force; const fy = dy / distance * force;
          a.vx -= fx; a.vy -= fy; b.vx += fx; b.vy += fy;
        }
      }
      edges.forEach(edge => {
        const dx = edge.target.x - edge.source.x; const dy = edge.target.y - edge.source.y;
        const distance = Math.max(1, Math.hypot(dx, dy));
        const desired = 72 + Math.min(120, Math.abs(dx) * .08);
        const force = (distance - desired) * .0024 * cooling;
        edge.source.vx += dx / distance * force; edge.source.vy += dy / distance * force;
        edge.target.vx -= dx / distance * force; edge.target.vy -= dy / distance * force;
      });
      nodes.forEach(node => {
        node.vx += (node.targetX - node.x) * .005;
        node.vy += (height / 2 - node.y) * .0007;
        node.vx *= .72; node.vy *= .72;
        node.x = clamp(node.x + node.vx, 45, width - 45);
        node.y = clamp(node.y + node.vy, 45, height - 45);
      });
    }
  }

  function mount(options) {
    const { root, records, hrefFor } = options;
    const canvas = root.querySelector('.archive-graph-canvas');
    const shell = root.querySelector('.archive-graph-shell');
    const tooltip = root.querySelector('.archive-graph-tooltip');
    const search = root.querySelector('.archive-graph-search');
    const suggestions = root.querySelector('.archive-graph-suggestions');
    const status = root.querySelector('.archive-graph-status');
    const { nodes, edges } = prepare(records);
    layout(nodes, edges);
    const context = canvas.getContext('2d');
    let pixelRatio = 1; let width = 1; let height = 1;
    let scale = 1; let offsetX = 0; let offsetY = 0;
    let hovered = null; let searchMatches = new Set(); let dragging = false; let moved = false;
    let pointerX = 0; let pointerY = 0; let startX = 0; let startY = 0; let startOffsetX = 0; let startOffsetY = 0;
    let disposed = false;
    const prominent = new Set([...nodes.filter(node => node.spotlight), ...[...nodes].sort((a, b) => b.incoming - a.incoming).slice(0, 12)]);
    const connected = new Set();
    edges.forEach(edge => { connected.add(edge.source); connected.add(edge.target); });

    const colors = () => {
      const style = getComputedStyle(document.documentElement);
      return {
        edge: style.getPropertyValue('--graph-edge').trim() || 'rgba(72, 98, 125, .24)',
        edgeOutgoing: style.getPropertyValue('--graph-edge-outgoing').trim() || '#d87532',
        edgeIncoming: style.getPropertyValue('--graph-edge-incoming').trim() || '#2c88bf',
        outline: style.getPropertyValue('--graph-node-outline').trim() || '#fff',
        label: style.getPropertyValue('--text').trim() || '#202733',
        muted: style.getPropertyValue('--muted').trim() || '#687386',
        halo: style.getPropertyValue('--graph-halo').trim() || 'rgba(40, 120, 181, .18)',
        spotlight: style.getPropertyValue('--graph-spotlight').trim() || '#b7791f'
      };
    };
    const toWorld = (x, y) => ({ x: (x - offsetX) / scale, y: (y - offsetY) / scale });
    const isEmphasized = edge => hovered && (edge.source === hovered || edge.target === hovered);
    const edgeRelation = edge => !hovered ? null : edge.source === hovered ? 'outgoing' : edge.target === hovered ? 'incoming' : null;

    function drawArrow(edge, color, alpha) {
      const source = edge.source; const target = edge.target;
      const dx = target.x - source.x; const dy = target.y - source.y;
      const distance = Math.max(1, Math.hypot(dx, dy));
      const ux = dx / distance; const uy = dy / distance;
      const endX = target.x - ux * (target.radius + 2.5 / scale);
      const endY = target.y - uy * (target.radius + 2.5 / scale);
      context.globalAlpha = alpha; context.strokeStyle = color;
      context.lineWidth = (isEmphasized(edge) ? 1.65 : .8) / scale;
      context.beginPath(); context.moveTo(source.x, source.y); context.lineTo(endX, endY); context.stroke();
      if (isEmphasized(edge) || scale >= .55) {
        const size = (isEmphasized(edge) ? 5.5 : 3.5) / scale;
        context.fillStyle = color; context.beginPath();
        context.moveTo(endX, endY);
        context.lineTo(endX - ux * size - uy * size * .62, endY - uy * size + ux * size * .62);
        context.lineTo(endX - ux * size + uy * size * .62, endY - uy * size - ux * size * .62);
        context.closePath(); context.fill();
      }
    }

    function draw() {
      if (disposed) return;
      const theme = colors();
      context.setTransform(pixelRatio, 0, 0, pixelRatio, 0, 0);
      context.clearRect(0, 0, width, height);
      context.save(); context.translate(offsetX, offsetY); context.scale(scale, scale);
      edges.forEach(edge => {
        const relation = edgeRelation(edge);
        const color = relation === 'outgoing' ? theme.edgeOutgoing : relation === 'incoming' ? theme.edgeIncoming : theme.edge;
        drawArrow(edge, color, hovered ? (relation ? .92 : .055) : .55);
      });
      nodes.forEach(node => {
        const related = !hovered || node === hovered || edges.some(edge => isEmphasized(edge) && (edge.source === node || edge.target === node));
        const searchVisible = !searchMatches.size || searchMatches.has(node);
        context.globalAlpha = related && searchVisible ? 1 : .16;
        if (node === hovered || searchMatches.has(node)) {
          context.fillStyle = theme.halo; context.beginPath(); context.arc(node.x, node.y, node.radius + 7 / scale, 0, Math.PI * 2); context.fill();
        }
        context.fillStyle = connected.has(node) ? node.color : theme.muted;
        context.strokeStyle = theme.outline; context.lineWidth = 1.5 / scale;
        context.beginPath(); context.arc(node.x, node.y, node.radius, 0, Math.PI * 2); context.fill(); context.stroke();
        if (node.spotlight) {
          context.strokeStyle = theme.spotlight; context.lineWidth = 2.2 / scale;
          context.beginPath(); context.arc(node.x, node.y, node.radius + 3.5 / scale, 0, Math.PI * 2); context.stroke();
        }
      });
      nodes.forEach(node => {
        if (node !== hovered && !searchMatches.has(node) && !(prominent.has(node) && scale > .46)) return;
        context.globalAlpha = node === hovered || !hovered ? 1 : .35;
        context.fillStyle = theme.label; context.font = `${node === hovered ? 600 : 500} ${11 / scale}px Arial, sans-serif`;
        context.textBaseline = 'middle';
        context.fillText(`#${archiveNumber(node.id)}`, node.x + node.radius + 5 / scale, node.y);
      });
      context.restore(); context.globalAlpha = 1;
    }

    function fit() {
      if (!nodes.length) return;
      const xs = nodes.map(node => node.x); const ys = nodes.map(node => node.y);
      const minX = Math.min(...xs) - 65; const maxX = Math.max(...xs) + 65;
      const minY = Math.min(...ys) - 65; const maxY = Math.max(...ys) + 65;
      scale = clamp(Math.min(width / Math.max(1, maxX - minX), height / Math.max(1, maxY - minY)) * .94, .18, 1.5);
      offsetX = width / 2 - (minX + maxX) / 2 * scale;
      offsetY = height / 2 - (minY + maxY) / 2 * scale;
      draw();
    }
    function resize() {
      const rect = canvas.getBoundingClientRect();
      const nextWidth = Math.max(1, Math.round(rect.width)); const nextHeight = Math.max(1, Math.round(rect.height));
      if (nextWidth === width && nextHeight === height) return;
      width = nextWidth; height = nextHeight; pixelRatio = Math.min(2, window.devicePixelRatio || 1);
      canvas.width = Math.round(width * pixelRatio); canvas.height = Math.round(height * pixelRatio);
      fit();
    }
    function zoom(factor, x = width / 2, y = height / 2) {
      const world = toWorld(x, y); const next = clamp(scale * factor, .16, 3.4);
      offsetX = x - world.x * next; offsetY = y - world.y * next; scale = next; draw();
    }
    function nodeAt(clientX, clientY) {
      const rect = canvas.getBoundingClientRect(); const world = toWorld(clientX - rect.left, clientY - rect.top);
      let found = null; let best = Infinity;
      nodes.forEach(node => {
        const distance = Math.hypot(node.x - world.x, node.y - world.y);
        const target = node.radius + 8 / scale;
        if (distance <= target && distance < best) { found = node; best = distance; }
      });
      return found;
    }
    function showTooltip(node, clientX, clientY) {
      if (!node) { tooltip.hidden = true; return; }
      tooltip.replaceChildren();
      const eyebrow = document.createElement('div'); eyebrow.className = 'archive-graph-tooltip-id'; eyebrow.textContent = `Archive #${archiveNumber(node.id)}`;
      const title = document.createElement('strong'); title.textContent = node.record.title;
      const byline = document.createElement('span'); byline.textContent = `${node.record.author} · Tick ${node.record.created_tick ?? '—'}`;
      const links = document.createElement('span'); links.textContent = `${node.incoming} citation${node.incoming === 1 ? '' : 's'} received`;
      tooltip.append(eyebrow, title, byline, links);
      if (node.spotlight) {
        const spotlight = document.createElement('span'); spotlight.className = 'archive-graph-tooltip-spotlight'; spotlight.textContent = 'Spotlight source';
        tooltip.append(spotlight);
      }
      tooltip.hidden = false;
      const shellRect = shell.getBoundingClientRect();
      const left = clamp(clientX - shellRect.left + 16, 12, shellRect.width - tooltip.offsetWidth - 12);
      const top = clamp(clientY - shellRect.top + 16, 12, shellRect.height - tooltip.offsetHeight - 12);
      tooltip.style.transform = `translate(${left}px, ${top}px)`;
    }
    function focusNode(node) {
      if (!node) return;
      searchMatches = new Set([node]); hovered = node;
      scale = Math.max(scale, 1.05);
      offsetX = width / 2 - node.x * scale; offsetY = height / 2 - node.y * scale;
      draw();
    }

    function onPointerDown(event) {
      dragging = true; moved = false; pointerX = startX = event.clientX; pointerY = startY = event.clientY;
      startOffsetX = offsetX; startOffsetY = offsetY; canvas.setPointerCapture(event.pointerId);
      canvas.classList.add('is-dragging');
    }
    function onPointerMove(event) {
      if (dragging) {
        const dx = event.clientX - startX; const dy = event.clientY - startY;
        if (Math.hypot(dx, dy) > 4) moved = true;
        offsetX = startOffsetX + dx; offsetY = startOffsetY + dy; tooltip.hidden = true; draw(); return;
      }
      pointerX = event.clientX; pointerY = event.clientY;
      const next = nodeAt(event.clientX, event.clientY);
      if (next !== hovered) { hovered = next; canvas.classList.toggle('has-node', Boolean(next)); draw(); }
      showTooltip(next, event.clientX, event.clientY);
    }
    function onPointerUp(event) {
      if (!dragging) return;
      dragging = false; canvas.classList.remove('is-dragging');
      const chosen = !moved ? nodeAt(event.clientX, event.clientY) : null;
      if (chosen) location.hash = hrefFor(chosen.record).replace(/^#/, '');
    }
    function onWheel(event) {
      event.preventDefault(); const rect = canvas.getBoundingClientRect();
      zoom(event.deltaY < 0 ? 1.13 : .885, event.clientX - rect.left, event.clientY - rect.top);
    }
    function applySearch() {
      const term = search.value.trim().toLowerCase();
      const exact = nodes.find(node => `Archive #${archiveNumber(node.id)} — ${node.record.title}`.toLowerCase() === term);
      searchMatches = exact ? new Set([exact]) : term ? new Set(nodes.filter(node => [node.id, node.record.title, node.record.author, node.record.lineage, node.spotlight ? 'spotlight' : ''].join(' ').toLowerCase().includes(term))) : new Set();
      if (searchMatches.size === 1) focusNode([...searchMatches][0]); else { hovered = null; tooltip.hidden = true; draw(); }
      status.textContent = term ? `${searchMatches.size} matching paper${searchMatches.size === 1 ? '' : 's'}` : `${nodes.length} papers · ${edges.length} citations`;
    }
    function onSearchKey(event) {
      if (event.key !== 'Enter') return;
      const match = [...nodes].find(node => `Archive #${archiveNumber(node.id)} — ${node.record.title}` === search.value) || [...searchMatches][0];
      if (match) focusNode(match);
    }
    function onKeyDown(event) {
      const amount = event.shiftKey ? 90 : 42;
      if (event.key === 'ArrowLeft') offsetX += amount;
      else if (event.key === 'ArrowRight') offsetX -= amount;
      else if (event.key === 'ArrowUp') offsetY += amount;
      else if (event.key === 'ArrowDown') offsetY -= amount;
      else if (event.key === '+' || event.key === '=') zoom(1.18);
      else if (event.key === '-') zoom(.85);
      else if (event.key === '0') fit();
      else if (event.key === 'Enter' && hovered) { location.hash = hrefFor(hovered.record).replace(/^#/, ''); return; }
      else return;
      event.preventDefault(); draw();
    }

    nodes.forEach(node => {
      const option = document.createElement('option'); option.value = `Archive #${archiveNumber(node.id)} — ${node.record.title}`; suggestions.appendChild(option);
    });
    status.textContent = `${nodes.length} papers · ${edges.length} citations`;
    canvas.addEventListener('pointerdown', onPointerDown); canvas.addEventListener('pointermove', onPointerMove);
    canvas.addEventListener('pointerup', onPointerUp); canvas.addEventListener('pointercancel', onPointerUp);
    canvas.addEventListener('pointerleave', () => { if (!dragging) { hovered = null; tooltip.hidden = true; canvas.classList.remove('has-node'); draw(); } });
    canvas.addEventListener('wheel', onWheel, { passive: false }); canvas.addEventListener('keydown', onKeyDown);
    search.addEventListener('input', applySearch); search.addEventListener('keydown', onSearchKey);
    root.querySelector('[data-graph-action="fit"]').addEventListener('click', fit);
    root.querySelector('[data-graph-action="in"]').addEventListener('click', () => zoom(1.2));
    root.querySelector('[data-graph-action="out"]').addEventListener('click', () => zoom(.83));
    const resizeObserver = new ResizeObserver(resize); resizeObserver.observe(canvas);
    const themeObserver = new MutationObserver(draw); themeObserver.observe(document.documentElement, { attributes: true, attributeFilter: ['data-theme'] });
    resize(); requestAnimationFrame(fit);

    return () => {
      disposed = true; resizeObserver.disconnect(); themeObserver.disconnect();
      canvas.replaceWith(canvas.cloneNode(true));
    };
  }

  window.StationArchiveGraph = { mount };
})();
