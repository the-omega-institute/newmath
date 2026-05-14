#!/usr/bin/env node
// Bake the dagre LR layered layout for the dossier dependency graph, run
// once at build time and written into dependency.json so the browser
// loads the visualization with `layout: preset` — no dagre, no client
// CPU. Same dagre params the page used to pass when it ran layout on
// every cold load.
import dagre from "dagre";

const NODE_WIDTH = 120;
const NODE_HEIGHT = 120;
const PARAMS = {
  rankdir: "LR",
  nodesep: 22,
  ranksep: 480,
  edgesep: 10,
  ranker: "network-simplex",
};

const chunks = [];
process.stdin.on("data", c => chunks.push(c));
process.stdin.on("end", () => {
  const data = JSON.parse(Buffer.concat(chunks).toString("utf8"));
  const g = new dagre.graphlib.Graph({ multigraph: false, compound: false })
    .setGraph(PARAMS)
    .setDefaultEdgeLabel(() => ({}));
  for (const n of data.nodes) g.setNode(n.id, { width: NODE_WIDTH, height: NODE_HEIGHT });
  for (const e of data.edges) {
    if (g.hasNode(e.source) && g.hasNode(e.target)) g.setEdge(e.source, e.target);
  }
  const t0 = Date.now();
  dagre.layout(g);
  const elapsed = Date.now() - t0;
  const positions = {};
  for (const n of data.nodes) {
    const p = g.node(n.id);
    if (p) positions[n.id] = [Math.round(p.x), Math.round(p.y)];
  }
  process.stderr.write(`[dagre-bake] ${data.nodes.length} nodes / ${data.edges.length} edges in ${elapsed}ms\n`);
  process.stdout.write(JSON.stringify(positions));
});
