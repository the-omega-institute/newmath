/**
 * cytoscape_override.js — Full-neighborhood cytoscape view for selected theorem.
 *
 * Public API:
 *   computeNeighborhood(startName, recordsByName, depth) → Set<string>
 *   renderCytoscapeNeighborhood(args) → { nodeCount, edgeCount, depth }
 */

// ---------------------------------------------------------------------------
// Neighborhood computation
// ---------------------------------------------------------------------------

/**
 * Pure function: compute the closure of names within depth-N from a starting
 * record, including BOTH upstream (record.dependencies) and downstream
 * (records that include this name in their dependencies).
 * Returns a Set of qualified names INCLUDING self.
 *
 * @param {string} startName
 * @param {Map<string,Object>} recordsByName
 * @param {number} depth - Hop limit
 * @returns {Set<string>}
 */
export function computeNeighborhood(startName, recordsByName, depth) {
  if (!recordsByName.has(startName)) return new Set([startName]);

  // Build reverse-index once: name → Set of names that depend on it
  const revIndex = new Map();
  for (const [name, rec] of recordsByName) {
    const deps = rec.dependencies || [];
    for (const dep of deps) {
      if (!revIndex.has(dep)) revIndex.set(dep, new Set());
      revIndex.get(dep).add(name);
    }
  }

  const visited = new Set([startName]);
  // BFS queue entries: [name, distanceFromStart]
  const queue = [[startName, 0]];

  while (queue.length > 0) {
    const [current, dist] = queue.shift();
    if (dist >= depth) continue;

    const rec = recordsByName.get(current);

    // Upstream: follow current's dependencies
    const ups = (rec && rec.dependencies) ? rec.dependencies : [];
    for (const dep of ups) {
      if (recordsByName.has(dep) && !visited.has(dep)) {
        visited.add(dep);
        queue.push([dep, dist + 1]);
      }
    }

    // Downstream: find all records that list current as a dependency
    const downs = revIndex.get(current) || new Set();
    for (const downstream of downs) {
      if (recordsByName.has(downstream) && !visited.has(downstream)) {
        visited.add(downstream);
        queue.push([downstream, dist + 1]);
      }
    }
  }

  return visited;
}

// ---------------------------------------------------------------------------
// Color mapping
// ---------------------------------------------------------------------------

function statusColor(status) {
  if (status === 'checked') return '#2d7a5f';
  if (status === 'stmt')    return '#5a86b3';
  return '#6b6b6b';
}

// Short label: last dot-segment of a qualified name
function shortLabel(name) {
  const parts = name.split('.');
  return parts[parts.length - 1];
}

// ---------------------------------------------------------------------------
// Cytoscape render
// ---------------------------------------------------------------------------

/**
 * Render a cytoscape view of the selected theorem's neighborhood (depth <= 2,
 * upstream + downstream).
 *
 * @param {Object} args
 * @param {Object} args.record - The selected theorem_graph record
 * @param {Map<string,Object>} args.recordsByName - All records keyed by name
 * @param {HTMLElement} args.container - DOM element to render into (cleared)
 * @param {Function} args.cytoscape - The cytoscape factory (window.cytoscape)
 * @param {Object} [args.opts]
 * @param {number} [args.opts.depth=2] - Neighborhood depth
 * @param {Function} [args.opts.onNodeClick] - Called with name when a node is tapped
 * @returns {{ nodeCount: number, edgeCount: number, depth: number }}
 */
export function renderCytoscapeNeighborhood({ record, recordsByName, container, cytoscape, opts = {} }) {
  const depth = opts.depth !== undefined ? opts.depth : 2;
  const onNodeClick = opts.onNodeClick || null;

  // Clear container and set explicit height for cytoscape
  container.innerHTML = '';
  container.style.width = container.style.width || '100%';
  container.style.height = container.style.height || '600px';

  const neighborhood = computeNeighborhood(record.name, recordsByName, depth);

  // Build nodes
  const nodes = [];
  for (const name of neighborhood) {
    const rec = recordsByName.get(name);
    const status = rec ? (rec.status || 'def-only') : 'def-only';
    const isStart = name === record.name;
    nodes.push({
      data: {
        id: name,
        label: shortLabel(name),
        fullName: name,
        status,
        color: statusColor(status),
        borderWidth: isStart ? 4 : 2,
        borderColor: isStart ? '#c45a4a' : '#ffffff',
      },
    });
  }

  // Build edges: a → b when b is in a.dependencies and both in neighborhood
  const edges = [];
  let edgeIdx = 0;
  for (const name of neighborhood) {
    const rec = recordsByName.get(name);
    if (!rec) continue;
    const deps = rec.dependencies || [];
    for (const dep of deps) {
      if (neighborhood.has(dep)) {
        edges.push({
          data: {
            id: 'e' + (edgeIdx++),
            source: name,
            target: dep,
          },
        });
      }
    }
  }

  const elements = [...nodes, ...edges];

  const cy = cytoscape({
    container,
    elements,
    style: [
      {
        selector: 'node',
        style: {
          'background-color': 'data(color)',
          'label': 'data(label)',
          'font-size': '11px',
          'font-family': 'ui-monospace, monospace',
          'color': '#222',
          'text-valign': 'bottom',
          'text-halign': 'center',
          'text-margin-y': 4,
          'width': 28,
          'height': 28,
          'border-width': 'data(borderWidth)',
          'border-color': 'data(borderColor)',
        },
      },
      {
        selector: 'edge',
        style: {
          'width': 1.5,
          'line-color': '#8a9bb0',
          'target-arrow-color': '#8a9bb0',
          'target-arrow-shape': 'triangle',
          'curve-style': 'bezier',
          'arrow-scale': 0.85,
          'opacity': 0.7,
        },
      },
      {
        selector: 'node:selected',
        style: {
          'border-width': 4,
          'border-color': '#f39c12',
          'overlay-color': '#f39c12',
          'overlay-opacity': 0.15,
        },
      },
    ],
    layout: {
      name: 'dagre',
      rankDir: 'LR',
      nodeSep: 30,
      rankSep: 80,
      padding: 20,
      fit: true,
      animate: false,
    },
    userZoomingEnabled: true,
    userPanningEnabled: true,
    boxSelectionEnabled: false,
    wheelSensitivity: 0.3,
  });

  if (onNodeClick) {
    cy.on('tap', 'node', (evt) => {
      const tgt = evt.target;
      if (tgt && tgt.isNode && tgt.isNode()) {
        onNodeClick(tgt.id());
      }
    });
  }

  return {
    nodeCount: nodes.length,
    edgeCount: edges.length,
    depth,
  };
}
