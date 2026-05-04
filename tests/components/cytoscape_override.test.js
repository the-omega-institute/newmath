import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { computeNeighborhood, renderCytoscapeNeighborhood } from '../../docs/dossier/components/cytoscape_override.js';

const RECORDS = [
  { name: 'A', kind: 'theorem', status: 'checked',  dependencies: ['B'],      paper_marker_sites: [] },
  { name: 'B', kind: 'theorem', status: 'stmt',     dependencies: ['C', 'D'], paper_marker_sites: [] },
  { name: 'C', kind: 'def',     status: 'def-only', dependencies: [],         paper_marker_sites: [] },
  { name: 'D', kind: 'theorem', status: 'stmt',     dependencies: [],         paper_marker_sites: [] },
  { name: 'E', kind: 'theorem', status: 'checked',  dependencies: ['A'],      paper_marker_sites: [] },
  { name: 'F', kind: 'theorem', status: 'stmt',     dependencies: [],         paper_marker_sites: [] },
];
const BY_NAME = new Map(RECORDS.map(r => [r.name, r]));

// ---------------------------------------------------------------------------
// computeNeighborhood
// ---------------------------------------------------------------------------

describe('computeNeighborhood', () => {
  it('depth 1 from B: includes B + upstream {C,D} + downstream {A}', () => {
    const n = computeNeighborhood('B', BY_NAME, 1);
    expect(n.has('B')).toBe(true);
    expect(n.has('C')).toBe(true);
    expect(n.has('D')).toBe(true);
    expect(n.has('A')).toBe(true);
    expect(n.has('E')).toBe(false); // E is depth 2 from B (via A)
    expect(n.has('F')).toBe(false);
  });

  it('depth 2 from B: includes E (via A)', () => {
    const n = computeNeighborhood('B', BY_NAME, 2);
    expect(n.has('E')).toBe(true);
  });

  it('always includes start node', () => {
    expect(computeNeighborhood('F', BY_NAME, 0).has('F')).toBe(true);
  });

  it('handles depth 0 = just self', () => {
    const n = computeNeighborhood('B', BY_NAME, 0);
    expect(n.size).toBe(1);
    expect(n.has('B')).toBe(true);
  });

  it('skips names not in recordsByName', () => {
    const sparse = new Map([
      ['A', { name: 'A', dependencies: ['MISSING'], paper_marker_sites: [] }],
    ]);
    const n = computeNeighborhood('A', sparse, 5);
    expect(n.size).toBe(1);
    expect(n.has('MISSING')).toBe(false);
  });
});

// ---------------------------------------------------------------------------
// renderCytoscapeNeighborhood
// ---------------------------------------------------------------------------

describe('renderCytoscapeNeighborhood', () => {
  let container;

  function makeStubCytoscape() {
    const calls = [];
    const factory = (config) => {
      calls.push(config);
      return { on: () => {} };
    };
    return { factory, calls };
  }

  beforeEach(() => {
    container = document.createElement('div');
    container.style.width = '800px';
    container.style.height = '600px';
    document.body.appendChild(container);
  });

  afterEach(() => {
    container.remove();
  });

  it('returns {nodeCount, edgeCount, depth}', () => {
    const stub = makeStubCytoscape();
    const r = renderCytoscapeNeighborhood({
      record: BY_NAME.get('B'),
      recordsByName: BY_NAME,
      container,
      cytoscape: stub.factory,
      opts: { depth: 1 },
    });
    expect(r.depth).toBe(1);
    expect(r.nodeCount).toBeGreaterThanOrEqual(2);
    expect(typeof r.edgeCount).toBe('number');
  });

  it('passes correct elements to cytoscape factory', () => {
    const stub = makeStubCytoscape();
    renderCytoscapeNeighborhood({
      record: BY_NAME.get('B'),
      recordsByName: BY_NAME,
      container,
      cytoscape: stub.factory,
      opts: { depth: 1 },
    });
    const config = stub.calls[0];
    const elements = config.elements;
    const nodes = elements.filter(e => e.data && !e.data.source);
    expect(nodes.find(n => n.data.id === 'B')).toBeDefined();
  });

  it('start node gets highlighted border (borderWidth=4, borderColor=#c45a4a)', () => {
    const stub = makeStubCytoscape();
    renderCytoscapeNeighborhood({
      record: BY_NAME.get('B'),
      recordsByName: BY_NAME,
      container,
      cytoscape: stub.factory,
      opts: { depth: 1 },
    });
    const config = stub.calls[0];
    const elements = config.elements;
    const startNode = elements.find(e => e.data && !e.data.source && e.data.id === 'B');
    expect(startNode).toBeDefined();
    expect(startNode.data.borderWidth).toBe(4);
    expect(startNode.data.borderColor).toBe('#c45a4a');
  });

  it('uses dagre layout with rankDir LR', () => {
    const stub = makeStubCytoscape();
    renderCytoscapeNeighborhood({
      record: BY_NAME.get('B'),
      recordsByName: BY_NAME,
      container,
      cytoscape: stub.factory,
      opts: { depth: 1 },
    });
    const config = stub.calls[0];
    expect(config.layout.name).toBe('dagre');
    expect(config.layout.rankDir).toBe('LR');
  });

  it('node-click fires opts.onNodeClick with name', () => {
    let clicked = null;

    const stub = (config) => {
      const handlers = {};
      const cy = {
        on: (event, sel, fn) => { handlers[event] = { sel, fn }; },
      };
      setTimeout(() => {
        if (handlers.tap) {
          handlers.tap.fn({
            target: {
              id: () => 'B',
              isNode: () => true,
            },
          });
        }
      }, 0);
      return cy;
    };

    renderCytoscapeNeighborhood({
      record: BY_NAME.get('B'),
      recordsByName: BY_NAME,
      container,
      cytoscape: stub,
      opts: {
        depth: 1,
        onNodeClick: (name) => { clicked = name; },
      },
    });

    return new Promise((res) => setTimeout(() => {
      expect(clicked).toBe('B');
      res();
    }, 50));
  });

  it('depth 0 from F produces single node, zero edges', () => {
    const stub = makeStubCytoscape();
    const r = renderCytoscapeNeighborhood({
      record: BY_NAME.get('F'),
      recordsByName: BY_NAME,
      container,
      cytoscape: stub.factory,
      opts: { depth: 0 },
    });
    expect(r.nodeCount).toBe(1);
    expect(r.edgeCount).toBe(0);
    expect(r.depth).toBe(0);
  });
});
