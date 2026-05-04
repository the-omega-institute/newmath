import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { renderTransitMap, renderTrustSummary } from '../../docs/dossier/components/transit-map.js';

// Stub dagre: assigns deterministic positions so tests don't need the real lib.
const STUB_DAGRE = {
  graphlib: {
    Graph: class {
      constructor() { this._nodes = new Map(); this._edges = []; this._cfg = {}; }
      setGraph(cfg)                { this._cfg = cfg; }
      setDefaultEdgeLabel(fn)      { this._edgeLabelFn = fn; }
      setNode(id, opts)            { this._nodes.set(id, { ...opts, x: 0, y: 0 }); }
      setEdge(src, dst)            { this._edges.push([src, dst]); }
      node(id)                     { return this._nodes.get(id); }
      nodes()                      { return [...this._nodes.keys()]; }
    },
  },
  layout(g) {
    let i = 0;
    for (const [id, n] of g._nodes) {
      n.x = 60 + (i % 5) * 160;
      n.y = 60 + Math.floor(i / 5) * 80;
      i++;
    }
  },
};

// ---------------------------------------------------------------------------
// Helpers to build minimal records
// ---------------------------------------------------------------------------

function makeRecord(overrides = {}) {
  return {
    name: 'Test.Foo',
    kind: 'theorem',
    status: 'checked',
    region: 'other',
    permalink: 'https://example.com/Foo',
    paper_marker_sites: [],
    dependencies: [],
    dep_file_imports: [],
    upstream_closure_summary: {
      axioms_count: 0, sorry_count: 0,
      defs_count: 0, theorems_count: 0, paper_markers_count: 0,
    },
    ...overrides,
  };
}

function makeMap(records) {
  return new Map(records.map(r => [r.name, r]));
}

// ---------------------------------------------------------------------------
// renderTrustSummary
// ---------------------------------------------------------------------------

describe('renderTrustSummary', () => {
  it('renders all 5 fields with project-stamp zeros', () => {
    const html = renderTrustSummary({
      axioms_count: 0, sorry_count: 0,
      defs_count: 14, theorems_count: 23, paper_markers_count: 5,
    });
    expect(html).toContain('0 axiom');
    expect(html).toContain('0 sorry');
    expect(html).toContain('14 def');
    expect(html).toContain('23 theorem');
    expect(html).toContain('5 paper marker');
  });

  it('passes through non-zero axiom/sorry counts without override', () => {
    const html = renderTrustSummary({
      axioms_count: 3, sorry_count: 1, defs_count: 0, theorems_count: 0, paper_markers_count: 0,
    });
    expect(html).toContain('3 axiom');
    expect(html).toContain('1 sorry');
  });

  it('returns HTML string with sober monospace styling', () => {
    const html = renderTrustSummary({
      axioms_count: 0, sorry_count: 0, defs_count: 0, theorems_count: 0, paper_markers_count: 0,
    });
    expect(typeof html).toBe('string');
    expect(html).toContain('monospace');
    expect(html).toContain('This claim depends on');
  });

  it('uses singular "sorry" (not "sorrys")', () => {
    const html = renderTrustSummary({
      axioms_count: 0, sorry_count: 1, defs_count: 0, theorems_count: 1, paper_markers_count: 1,
    });
    expect(html).not.toContain('sorrys');
  });
});

// ---------------------------------------------------------------------------
// renderTransitMap
// ---------------------------------------------------------------------------

describe('renderTransitMap', () => {
  let container;

  beforeEach(() => {
    container = document.createElement('div');
    document.body.appendChild(container);
  });

  afterEach(() => {
    container.remove();
  });

  it('empty closure: renders just self + Trust Summary', () => {
    const rec = makeRecord({ name: 'Root.Theorem', dependencies: [] });
    const map = makeMap([rec]);

    const result = renderTransitMap({
      record: rec, recordsByName: map, container,
      opts: { dagre: STUB_DAGRE },
    });

    expect(result.didSuggestCytoscape).toBe(false);
    expect(container.innerHTML).toContain('tm-trust');
    const stations = container.querySelectorAll('.tm-station');
    expect(stations.length).toBeGreaterThanOrEqual(1);
  });

  it('single node closure renders one station', () => {
    const rec = makeRecord({ name: 'Solo.Def', kind: 'def', dependencies: [] });
    const map = makeMap([rec]);

    renderTransitMap({
      record: rec, recordsByName: map, container,
      opts: { dagre: STUB_DAGRE },
    });

    const stations = container.querySelectorAll('.tm-station');
    expect(stations.length).toBe(1);
  });

  it('two-node chain: upstream dep is rendered as a station', () => {
    const dep = makeRecord({ name: 'Dep.Lemma', kind: 'lemma', dependencies: [] });
    const root = makeRecord({
      name: 'Root.Theorem', kind: 'theorem',
      dependencies: ['Dep.Lemma'],
      upstream_closure_summary: { axioms_count: 0, sorry_count: 0, defs_count: 0, theorems_count: 1, paper_markers_count: 0 },
    });
    const map = makeMap([dep, root]);

    renderTransitMap({
      record: root, recordsByName: map, container,
      opts: { dagre: STUB_DAGRE },
    });

    const stations = container.querySelectorAll('.tm-station');
    expect(stations.length).toBe(2);
  });

  it('chain-collapse WITHOUT paper-marker: 3-node linear chain folds to hidden badge', () => {
    // A → B → C, none have paper_marker_sites → B is collapsible
    const a = makeRecord({ name: 'Chain.A', kind: 'def', dependencies: [] });
    const b = makeRecord({ name: 'Chain.B', kind: 'def', dependencies: ['Chain.A'], paper_marker_sites: [] });
    const c = makeRecord({ name: 'Chain.C', kind: 'theorem', dependencies: ['Chain.B'], paper_marker_sites: [] });
    const map = makeMap([a, b, c]);

    renderTransitMap({
      record: c, recordsByName: map, container,
      opts: { dagre: STUB_DAGRE },
    });

    // Chain A→B→C: A is head with 2 hidden (B,C collapsed), or A→B collapsed
    // Either way: svg should contain a '+N hidden' badge for the compressed chain
    const svgText = container.querySelector('svg')?.innerHTML || container.innerHTML;
    expect(svgText).toContain('hidden');
  });

  it('INVARIANT: paper-marker station is NEVER collapsed — 3-node chain with paper marker in middle always renders all 3', () => {
    // A → B → C, where B has paper_marker_sites (ineligible for collapse)
    const a = makeRecord({ name: 'PaperChain.A', kind: 'def', dependencies: [] });
    const b = makeRecord({
      name: 'PaperChain.B', kind: 'theorem',
      dependencies: ['PaperChain.A'],
      paper_marker_sites: [{ tex_file: 'papers/bedc/foo.tex', label: 'thm:foo', pdf_anchor: 'thm.foo', marker_kind: 'leanchecked' }],
    });
    const c = makeRecord({
      name: 'PaperChain.C', kind: 'theorem',
      dependencies: ['PaperChain.B'],
      paper_marker_sites: [],
    });
    const map = makeMap([a, b, c]);

    renderTransitMap({
      record: c, recordsByName: map, container,
      opts: { dagre: STUB_DAGRE },
    });

    const svgEl = container.querySelector('svg');
    expect(svgEl).not.toBeNull();
    const svgText = svgEl.innerHTML;

    // B must appear as its own station (not collapsed)
    const bStation = svgEl.querySelector('[data-id="PaperChain.B"]');
    expect(bStation).not.toBeNull();

    // No '+N hidden' badge should appear — nothing is collapsible with B in the middle
    expect(svgText).not.toContain('hidden');

    // All 3 stations must be present
    const stations = svgEl.querySelectorAll('.tm-station');
    expect(stations.length).toBe(3);
  });

  it('large graph (>80 nodes) shows density banner, no SVG rendered', () => {
    // Create a root with 81 unique deps (each dep has no further deps)
    const deps = Array.from({ length: 81 }, (_, i) =>
      makeRecord({ name: `Dense.Dep${i}`, kind: 'def', dependencies: [] })
    );
    const root = makeRecord({
      name: 'Dense.Root',
      dependencies: deps.map(d => d.name),
      upstream_closure_summary: {
        axioms_count: 0, sorry_count: 0,
        defs_count: 81, theorems_count: 0, paper_markers_count: 0,
      },
    });
    const map = makeMap([root, ...deps]);

    const result = renderTransitMap({
      record: root, recordsByName: map, container,
      opts: { dagre: STUB_DAGRE, maxNodesBeforeCytoscapeSuggestion: 80 },
    });

    expect(result.didSuggestCytoscape).toBe(true);
    expect(container.innerHTML).toContain('upstream nodes');
    expect(container.innerHTML).toContain('Render anyway');
    expect(container.querySelector('svg')).toBeNull();
  });

  it('renders Trust Summary widget at top of container', () => {
    const rec = makeRecord({
      name: 'Summary.Test',
      upstream_closure_summary: {
        axioms_count: 0, sorry_count: 0,
        defs_count: 7, theorems_count: 3, paper_markers_count: 2,
      },
    });
    const map = makeMap([rec]);

    renderTransitMap({
      record: rec, recordsByName: map, container,
      opts: { dagre: STUB_DAGRE },
    });

    const trust = container.querySelector('.tm-trust-summary');
    expect(trust).not.toBeNull();
    expect(trust.textContent).toContain('7 def');
    expect(trust.textContent).toContain('3 theorem');
    expect(trust.textContent).toContain('2 paper marker');

    // Trust summary should come before SVG in DOM order
    const children = [...container.querySelectorAll('.tm-trust-wrapper, svg.tm-svg')];
    const trustIdx = children.findIndex(el => el.classList.contains('tm-trust-wrapper'));
    const svgIdx   = children.findIndex(el => el.tagName === 'SVG');
    if (trustIdx !== -1 && svgIdx !== -1) {
      expect(trustIdx).toBeLessThan(svgIdx);
    }
  });

  it('5 station shapes: inductive, def, structure, theorem, paper_marker all render', () => {
    // Root depends on ALL four leaf records (diamond topology) — in-degree > 1
    // prevents any chain-collapse, so all 5 nodes render as distinct stations.
    const records = [
      makeRecord({ name: 'Shape.Inductive', kind: 'inductive', status: 'def-only', dependencies: [] }),
      makeRecord({ name: 'Shape.Def',       kind: 'def',       status: 'def-only', dependencies: [] }),
      makeRecord({ name: 'Shape.Struct',    kind: 'structure', status: 'def-only', dependencies: [] }),
      makeRecord({ name: 'Shape.Theorem',   kind: 'theorem',   status: 'checked',  dependencies: [] }),
      makeRecord({
        name: 'Shape.Root', kind: 'theorem', status: 'stmt',
        dependencies: ['Shape.Inductive', 'Shape.Def', 'Shape.Struct', 'Shape.Theorem'],
        paper_marker_sites: [{ tex_file: 'papers/x.tex', label: 'thm:x', pdf_anchor: 'thm.x', marker_kind: 'leanchecked' }],
      }),
    ];
    const map = makeMap(records);

    renderTransitMap({
      record: records[4], recordsByName: map, container,
      opts: { dagre: STUB_DAGRE },
    });

    const svgEl = container.querySelector('svg');
    expect(svgEl).not.toBeNull();
    // All 5 records render as distinct stations (no linear chain to collapse).
    const stations = svgEl.querySelectorAll('.tm-station');
    expect(stations.length).toBe(5);

    // Inductive uses <circle>
    const inductiveStation = svgEl.querySelector('[data-id="Shape.Inductive"]');
    expect(inductiveStation).not.toBeNull();
    expect(inductiveStation.querySelector('circle')).not.toBeNull();

    // Theorem uses <rect> with rx=16
    const theoremStation = svgEl.querySelector('[data-id="Shape.Theorem"]');
    expect(theoremStation).not.toBeNull();
    const rects = theoremStation.querySelectorAll('rect');
    const rounded = [...rects].some(r => r.getAttribute('rx') === '16');
    expect(rounded).toBe(true);
  });
});
