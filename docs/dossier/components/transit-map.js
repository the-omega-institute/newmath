/**
 * transit-map.js — Proof-Obligation Transit Map + Trust Summary widget.
 *
 * Public API:
 *   renderTransitMap(args) → { stationCount, lineCount, didSuggestCytoscape }
 *   renderTrustSummary(summary) → string (HTML)
 */

// ---------------------------------------------------------------------------
// Utilities
// ---------------------------------------------------------------------------

function escapeHtml(text) {
  return String(text)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

// ---------------------------------------------------------------------------
// Trust Summary widget
// ---------------------------------------------------------------------------

/**
 * Render the Trust Summary widget.
 *
 * @param {Object} summary - record.upstream_closure_summary
 * @param {number} summary.axioms_count
 * @param {number} summary.sorry_count
 * @param {number} summary.defs_count
 * @param {number} summary.theorems_count
 * @param {number} summary.paper_markers_count
 * @returns {string} HTML string
 */
export function renderTrustSummary(summary) {
  const ax = Number(summary.axioms_count ?? 0);
  const so = Number(summary.sorry_count ?? 0);
  const de = Number(summary.defs_count ?? 0);
  const th = Number(summary.theorems_count ?? 0);
  const pm = Number(summary.paper_markers_count ?? 0);

  function badge(n, singular, plural) {
    const label = n === 1 ? singular : (plural !== undefined ? plural : singular + 's');
    const text = `${n} ${escapeHtml(label)}`;
    return (
      `<span class="tm-trust-count" ` +
      `style="border-bottom:1px dotted #888;font-variant-numeric:tabular-nums">` +
      `${text}</span>`
    );
  }

  return (
    `<div class="tm-trust-summary" style="` +
    `font-family:monospace;font-size:0.82em;color:#555;` +
    `padding:6px 10px;border-left:2px solid #ccc;margin-bottom:10px;` +
    `background:#f9f9f9;line-height:1.6` +
    `">` +
    `This claim depends on: ` +
    badge(ax, 'axiom') + ` \xb7 ` +
    badge(so, 'sorry', 'sorry') + ` \xb7 ` +
    badge(de, 'def') + ` \xb7 ` +
    badge(th, 'theorem') + ` \xb7 ` +
    badge(pm, 'paper marker') +
    `</div>`
  );
}

// ---------------------------------------------------------------------------
// Station shapes
// ---------------------------------------------------------------------------

const STATUS_COLOR = {
  checked:    '#2d7a5f',
  stmt:       '#5a86b3',
  'def-only': '#6b6b6b',
};

function stationColor(status) {
  return STATUS_COLOR[status] || '#8a8a8a';
}

function stationShape(kind, cx, cy, color, label, id) {
  const col   = escapeHtml(color);
  const eid   = escapeHtml(id);
  const elabel = escapeHtml(label.length > 22 ? label.slice(0, 20) + '…' : label);

  let shape;
  if (kind === 'inductive') {
    shape = `<circle cx="${cx}" cy="${cy}" r="18" fill="${col}" stroke="white" stroke-width="1.5"/>`;
  } else if (kind === 'structure') {
    const d = 20;
    shape = (
      `<polygon points="${cx},${cy - d} ${cx + d},${cy} ${cx},${cy + d} ${cx - d},${cy}" ` +
      `fill="${col}" stroke="white" stroke-width="1.5"/>`
    );
  } else if (kind === 'theorem' || kind === 'lemma') {
    shape = (
      `<rect x="${cx - 40}" y="${cy - 16}" width="80" height="32" rx="16" ` +
      `fill="${col}" stroke="white" stroke-width="1.5"/>`
    );
  } else if (kind === 'paper_marker') {
    const r = 18;
    const pts = Array.from({ length: 5 }, (_, i) => {
      const angle = (i * 2 * Math.PI / 5) - Math.PI / 2;
      return `${cx + r * Math.cos(angle)},${cy + r * Math.sin(angle)}`;
    }).join(' ');
    shape = `<polygon points="${pts}" fill="${col}" stroke="white" stroke-width="1.5"/>`;
  } else {
    shape = (
      `<rect x="${cx - 22}" y="${cy - 18}" width="44" height="36" rx="4" ` +
      `fill="${col}" stroke="white" stroke-width="1.5"/>`
    );
  }

  return (
    `<g class="tm-station" data-id="${eid}" style="cursor:pointer">` +
    shape +
    `<text x="${cx}" y="${cy + 30}" text-anchor="middle" font-size="9" fill="#444" ` +
    `font-family="monospace">${elabel}</text>` +
    `</g>`
  );
}

// ---------------------------------------------------------------------------
// Chain-collapse helpers
// ---------------------------------------------------------------------------

/**
 * Build in-degree / out-degree and successor/predecessor maps for a node set.
 * Only counts edges where BOTH endpoints are in the node set.
 */
function buildGraph(nodes, recordsByName) {
  const inDeg  = new Map();
  const outDeg = new Map();
  const succ   = new Map();
  const pred   = new Map();

  for (const name of nodes) {
    inDeg.set(name, 0);
    outDeg.set(name, 0);
    succ.set(name, []);
    pred.set(name, []);
  }

  for (const name of nodes) {
    const rec = recordsByName.get(name);
    if (!rec) continue;
    for (const dep of (rec.dependencies || [])) {
      if (!nodes.has(dep)) continue;
      outDeg.set(dep, (outDeg.get(dep) || 0) + 1);
      inDeg.set(name, (inDeg.get(name) || 0) + 1);
      succ.get(dep).push(name);
      pred.get(name).push(dep);
    }
  }

  return { inDeg, outDeg, succ, pred };
}

/**
 * Find collapsible chains: maximal sub-paths where every node has
 * in-degree=1 AND out-degree=1 AND no paper_marker_sites.
 *
 * Critical invariant: any node with paper_marker_sites.length > 0
 * is collapse-INELIGIBLE and always rendered as its own station.
 *
 * Returns: Map<string, string[]> where key = chain head (first node),
 * value = full ordered chain [head, ..., tail].
 * Only chains of length >= 3 are returned.
 */
function findCollapseChains(nodes, recordsByName) {
  const { inDeg, outDeg, succ } = buildGraph(nodes, recordsByName);

  function isEligible(name) {
    const rec = recordsByName.get(name);
    if (!rec) return false;
    return !rec.paper_marker_sites || rec.paper_marker_sites.length === 0;
  }

  // A chain can only start at a node that is not in the interior of a chain.
  // Interior nodes have: inDeg=1, outDeg=1, and are eligible.
  // Chain start nodes: NOT (inDeg=1 AND outDeg=1 AND eligible),
  // i.e., inDeg!=1 OR outDeg!=1 OR !eligible.
  // We walk forward from each start node along eligible pass-through nodes.

  const chains = new Map();
  const assignedToChain = new Set(); // track all nodes claimed by any chain

  // Collect chain-start candidates: inDeg != 1 OR outDeg != 1 OR !eligible
  // Plus: any node not yet reached (to handle isolated nodes).
  const starts = new Set();
  for (const name of nodes) {
    const ind = inDeg.get(name) || 0;
    const outd = outDeg.get(name) || 0;
    if (ind !== 1 || outd !== 1 || !isEligible(name)) {
      starts.add(name);
    }
  }

  for (const startName of starts) {
    const chain = [startName];
    let cur = startName;

    while (true) {
      const nexts = succ.get(cur) || [];
      if (nexts.length !== 1) break;
      const nx = nexts[0];
      if (assignedToChain.has(nx)) break;
      if ((inDeg.get(nx) || 0) !== 1) break;
      if (!isEligible(nx)) break;
      if (!isEligible(cur) && cur !== startName) break;
      chain.push(nx);
      cur = nx;
    }

    if (chain.length >= 3) {
      for (const n of chain) assignedToChain.add(n);
      chains.set(startName, chain);
    }
  }

  return chains;
}

// ---------------------------------------------------------------------------
// BFS upstream closure
// ---------------------------------------------------------------------------

function computeClosure(record, recordsByName) {
  const visited = new Set();
  const queue   = [record.name];
  while (queue.length > 0) {
    const name = queue.shift();
    if (visited.has(name)) continue;
    visited.add(name);
    const rec = recordsByName.get(name);
    if (!rec) continue;
    for (const dep of (rec.dependencies || [])) {
      if (!visited.has(dep)) queue.push(dep);
    }
  }
  return visited;
}

// ---------------------------------------------------------------------------
// Deterministic synthetic layout (fallback when dagre unavailable)
// ---------------------------------------------------------------------------

/**
 * Assigns (x, y) using topological depth BFS layout.
 * Returns Map<name, {x, y, width, height}>.
 */
function syntheticLayout(nodes, recordsByName) {
  const { inDeg } = buildGraph(nodes, recordsByName);

  const depth = new Map();
  const queue = [];
  for (const [name, d] of inDeg) {
    if (d === 0) { depth.set(name, 0); queue.push(name); }
  }

  while (queue.length > 0) {
    const name = queue.shift();
    const rec  = recordsByName.get(name);
    if (!rec) continue;
    for (const dep of (rec.dependencies || [])) {
      if (!nodes.has(dep)) continue;
      const nd = (depth.get(name) || 0) + 1;
      if (!depth.has(dep) || depth.get(dep) < nd) {
        depth.set(dep, nd);
        queue.push(dep);
      }
    }
  }

  const byDepth = new Map();
  for (const name of nodes) {
    const d = depth.get(name) || 0;
    if (!byDepth.has(d)) byDepth.set(d, []);
    byDepth.get(d).push(name);
  }

  const layout = new Map();
  const XSTEP  = 160, YSTEP = 80;
  for (const [d, group] of byDepth) {
    group.forEach((name, i) => {
      layout.set(name, { x: 60 + i * XSTEP, y: 60 + d * YSTEP, width: 80, height: 36 });
    });
  }
  return layout;
}

// ---------------------------------------------------------------------------
// Dagre layout wrapper
// ---------------------------------------------------------------------------

function dagreLayout(nodes, recordsByName, dagre) {
  const g = new dagre.graphlib.Graph();
  g.setGraph({ rankdir: 'TB', nodesep: 60, ranksep: 100, marginx: 40, marginy: 40 });
  g.setDefaultEdgeLabel(() => ({}));

  for (const name of nodes) {
    g.setNode(name, { width: 80, height: 36 });
  }
  for (const name of nodes) {
    const rec = recordsByName.get(name);
    if (!rec) continue;
    for (const dep of (rec.dependencies || [])) {
      if (nodes.has(dep)) g.setEdge(dep, name);
    }
  }

  dagre.layout(g);

  const layout = new Map();
  for (const name of nodes) {
    const n = g.node(name);
    layout.set(name, { x: n.x, y: n.y, width: n.width, height: n.height });
  }
  return layout;
}

// ---------------------------------------------------------------------------
// SVG builder
// ---------------------------------------------------------------------------

function buildSvg(visibleNodes, collapsedChains, layout, recordsByName) {
  let maxX = 100, maxY = 100;
  for (const [, pos] of layout) {
    if (pos.x + 60 > maxX) maxX = pos.x + 60;
    if (pos.y + 60 > maxY) maxY = pos.y + 60;
  }
  const svgW = maxX + 80;
  const svgH = maxY + 80;

  const edgePaths     = [];
  const stationGroups = [];
  const hoverData     = [];

  const collapsedInternals = new Set();
  const chainByHead        = new Map();
  for (const [head, chain] of collapsedChains) {
    for (let i = 1; i < chain.length; i++) collapsedInternals.add(chain[i]);
    chainByHead.set(head, chain);
  }

  for (const name of visibleNodes) {
    if (collapsedInternals.has(name)) continue;
    const rec    = recordsByName.get(name);
    if (!rec) continue;
    const toPos  = layout.get(name);
    if (!toPos) continue;

    for (const dep of (rec.dependencies || [])) {
      if (!visibleNodes.has(dep)) continue;
      if (collapsedInternals.has(dep)) continue;
      const fromPos = layout.get(dep);
      if (!fromPos) continue;

      const x1 = fromPos.x, y1 = fromPos.y;
      const x2 = toPos.x,   y2 = toPos.y;
      edgePaths.push(
        `<path d="M${x1},${y1} Q${(x1 + x2) / 2},${(y1 + y2) / 2} ${x2},${y2}" ` +
        `fill="none" stroke="#8a8a8a" stroke-width="3" stroke-linecap="round" class="tm-edge"/>`
      );
    }
  }

  for (const name of visibleNodes) {
    if (collapsedInternals.has(name)) continue;
    const rec = recordsByName.get(name);
    if (!rec) continue;
    const pos = layout.get(name);
    if (!pos) continue;

    const { x, y } = pos;
    const color     = stationColor(rec.status);
    const shortName = name.split('.').pop() || name;

    if (chainByHead.has(name)) {
      const chain      = chainByHead.get(name);
      const hiddenCount = chain.length - 1;
      const eid        = escapeHtml(name);
      stationGroups.push(
        `<g class="tm-station tm-chain-head" data-id="${eid}" ` +
        `data-chain-len="${chain.length}" style="cursor:pointer">` +
        `<rect x="${x - 45}" y="${y - 18}" width="90" height="36" rx="8" ` +
        `fill="${escapeHtml(color)}" stroke="white" stroke-width="1.5"/>` +
        `<text x="${x}" y="${y + 5}" text-anchor="middle" font-size="9" ` +
        `fill="white" font-family="monospace">+${hiddenCount} hidden</text>` +
        `</g>`
      );
    } else {
      stationGroups.push(stationShape(rec.kind, x, y, color, shortName, name));
    }

    hoverData.push({ id: name, record: rec, x, y });
  }

  const svgContent = [
    `<svg xmlns="http://www.w3.org/2000/svg" width="${svgW}" height="${svgH}" ` +
    `class="tm-svg" style="font-family:monospace;display:block;max-width:100%;overflow:visible">`,
    ...edgePaths,
    ...stationGroups,
    `</svg>`,
  ].join('\n');

  return { svgContent, hoverData, edgeCount: edgePaths.length };
}

// ---------------------------------------------------------------------------
// Hover panel
// ---------------------------------------------------------------------------

function attachHoverPanel(container, hoverData, glossary, renderStatement, opts) {
  const { paperPdfUrl = '' } = opts || {};

  const panel = document.createElement('div');
  panel.className = 'tm-hover-panel';
  panel.style.cssText = [
    'position:absolute',
    'background:#fff',
    'border:1px solid #ccc',
    'border-radius:4px',
    'padding:8px 10px',
    'font-family:monospace',
    'font-size:0.78em',
    'max-width:340px',
    'z-index:100',
    'pointer-events:none',
    'display:none',
    'box-shadow:0 2px 8px rgba(0,0,0,0.12)',
    'line-height:1.5',
  ].join(';');
  container.style.position = 'relative';
  container.appendChild(panel);

  const svgEl = container.querySelector('svg.tm-svg');
  if (!svgEl) return;

  svgEl.querySelectorAll('.tm-station').forEach(el => {
    const id    = el.getAttribute('data-id');
    const entry = hoverData.find(h => h.id === id);
    if (!entry) return;

    el.addEventListener('mouseenter', () => {
      const rec         = entry.record;
      const svgRect     = svgEl.getBoundingClientRect();
      const cRect       = container.getBoundingClientRect();
      const px          = entry.x + (svgRect.left - cRect.left) + 20;
      const py          = entry.y + (svgRect.top  - cRect.top)  - 10;

      let html = `<div style="font-weight:bold;color:#333">${escapeHtml(rec.name)}</div>`;
      html    += `<div style="color:#888">${escapeHtml(rec.kind)} `;

      const sstyle = `background:${stationColor(rec.status)};color:white;` +
        `padding:0 4px;border-radius:3px;font-size:0.85em`;
      html += `<span style="${sstyle}">${escapeHtml(rec.status)}</span></div>`;

      if (rec.region) {
        html += `<div style="color:#aaa;font-size:0.85em">${escapeHtml(rec.region)}</div>`;
      }

      if (rec.statement && glossary && renderStatement) {
        const rendered = renderStatement(rec.statement, glossary);
        if (rendered.tier === 3) {
          html += `<div style="margin-top:4px">` +
            `<span style="background:#e8e8e8;padding:0 3px;border-radius:2px;font-size:0.75em">` +
            `raw lean</span> ${rendered.html}</div>`;
        } else {
          html += `<div style="margin-top:4px">${rendered.html}</div>`;
        }
      }

      if (rec.permalink) {
        html += `<div style="margin-top:6px">` +
          `<a href="${escapeHtml(rec.permalink)}" target="_blank" rel="noopener" ` +
          `style="color:#5a86b3;text-decoration:none">view source ↗</a></div>`;
      }

      if (rec.paper_marker_sites && rec.paper_marker_sites.length > 0) {
        html += `<div style="margin-top:4px;color:#888;font-size:0.85em">Paper markers:</div>`;
        for (const site of rec.paper_marker_sites) {
          const anchor = site.pdf_anchor ? `#${site.pdf_anchor}` : '';
          const href   = paperPdfUrl ? `${paperPdfUrl}${anchor}` : '#';
          html += `<div><a href="${escapeHtml(href)}" target="_blank" rel="noopener" ` +
            `style="color:#5a86b3;text-decoration:none">` +
            `${escapeHtml(site.tex_file)}:${escapeHtml(site.label)} ↗</a></div>`;
        }
      }

      panel.innerHTML  = html;
      panel.style.left = `${px}px`;
      panel.style.top  = `${py}px`;
      panel.style.display = 'block';
    });

    el.addEventListener('mouseleave', () => { panel.style.display = 'none'; });
  });
}

// ---------------------------------------------------------------------------
// Internal render
// ---------------------------------------------------------------------------

function _renderMap({ record, recordsByName, container, glossary, renderStmt,
                      paperPdfUrl, githubBlobBase, dagre, knownClosure }) {
  const trustDiv = document.createElement('div');
  trustDiv.className  = 'tm-trust-wrapper';
  trustDiv.style.cssText = 'position:sticky;top:0;z-index:10;';
  trustDiv.innerHTML  = renderTrustSummary(record.upstream_closure_summary || {});
  container.appendChild(trustDiv);

  const layout = (dagre && dagre.graphlib && dagre.layout)
    ? dagreLayout(knownClosure, recordsByName, dagre)
    : syntheticLayout(knownClosure, recordsByName);

  const chains = findCollapseChains(knownClosure, recordsByName);

  const { svgContent, hoverData } = buildSvg(knownClosure, chains, layout, recordsByName);

  const svgWrapper = document.createElement('div');
  svgWrapper.className   = 'tm-svg-wrapper';
  svgWrapper.style.cssText = 'overflow-x:auto;';
  svgWrapper.innerHTML   = svgContent;
  container.appendChild(svgWrapper);

  attachHoverPanel(container, hoverData, glossary, renderStmt, { paperPdfUrl, githubBlobBase });
}

// ---------------------------------------------------------------------------
// Main: renderTransitMap
// ---------------------------------------------------------------------------

/**
 * Render a transit map for the given theorem record.
 *
 * @param {Object} args
 * @param {Object} args.record
 * @param {Map<string,Object>} args.recordsByName
 * @param {HTMLElement} args.container
 * @param {Object} [args.glossary]
 * @param {Function} [args.renderStatement]
 * @param {Object} [args.opts]
 * @param {string}   [args.opts.paperPdfUrl]
 * @param {string}   [args.opts.githubBlobBase]
 * @param {number}   [args.opts.maxNodesBeforeCytoscapeSuggestion=80]
 * @param {Object}   [args.opts.dagre]
 * @returns {{ stationCount: number, lineCount: number, didSuggestCytoscape: boolean }}
 */
export function renderTransitMap(args) {
  const {
    record,
    recordsByName,
    container,
    glossary = {},
    renderStatement: renderStmt = null,
    opts = {},
  } = args;

  const {
    paperPdfUrl = '',
    githubBlobBase = '',
    maxNodesBeforeCytoscapeSuggestion = 80,
    dagre = null,
  } = opts;

  container.innerHTML = '';

  const closure      = computeClosure(record, recordsByName);
  const knownClosure = new Set([...closure].filter(n => recordsByName.has(n)));

  if (knownClosure.size > maxNodesBeforeCytoscapeSuggestion) {
    const banner = document.createElement('div');
    banner.className   = 'tm-density-banner';
    banner.style.cssText = [
      'font-family:monospace', 'font-size:0.85em', 'color:#555',
      'border:1px dashed #aaa', 'padding:10px 14px', 'border-radius:4px',
      'background:#fafafa', 'margin-bottom:8px',
    ].join(';');
    banner.textContent =
      `This claim has ${knownClosure.size} upstream nodes — the transit map view may be ` +
      `hard to read. Consider switching to ‘full graph’ view for a different layout.`;

    const btn = document.createElement('button');
    btn.textContent    = 'Render anyway';
    btn.style.cssText  = 'margin-left:10px;font-family:monospace;cursor:pointer';
    banner.appendChild(btn);
    container.appendChild(banner);

    btn.addEventListener('click', () => {
      container.innerHTML = '';
      _renderMap({ record, recordsByName, container, glossary, renderStmt,
                   paperPdfUrl, githubBlobBase, dagre, knownClosure });
    });

    return { stationCount: knownClosure.size, lineCount: 0, didSuggestCytoscape: true };
  }

  _renderMap({ record, recordsByName, container, glossary, renderStmt,
               paperPdfUrl, githubBlobBase, dagre, knownClosure });

  const svgEl       = container.querySelector('svg.tm-svg');
  const stationCount = svgEl ? svgEl.querySelectorAll('.tm-station').length : 0;
  const lineCount    = svgEl ? svgEl.querySelectorAll('.tm-edge').length    : 0;

  return { stationCount, lineCount, didSuggestCytoscape: false };
}
