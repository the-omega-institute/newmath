(function (global) {
  "use strict";

  const RULE110 = [0, 1, 1, 1, 0, 1, 1, 0];

  function normalizeInitial(initial) {
    if (initial instanceof Uint8Array) {
      return new Uint8Array(initial);
    }
    if (Array.isArray(initial)) {
      return Uint8Array.from(initial);
    }
    if (typeof initial === "string") {
      const row = new Uint8Array(initial.length);
      for (let i = 0; i < initial.length; i++) {
        row[i] = initial.charCodeAt(i) === 49 ? 1 : 0;
      }
      return row;
    }
    return new Uint8Array(0);
  }

  function step(row) {
    const n = row.length;
    const next = new Uint8Array(n);
    for (let i = 0; i < n; i++) {
      const l = i > 0 ? row[i - 1] : 0;
      const c = row[i];
      const r = i < n - 1 ? row[i + 1] : 0;
      next[i] = RULE110[(l << 2) | (c << 1) | r];
    }
    return next;
  }

  function evolve(initial, steps) {
    const count = Math.max(1, Number.isFinite(steps) ? Math.floor(steps) : 1);
    const rows = [normalizeInitial(initial)];
    let cur = rows[0];
    for (let t = 1; t < count; t++) {
      cur = step(cur);
      rows.push(cur);
    }
    return rows;
  }

  global.Rule110Evolve = {
    step,
    evolve
  };
})(window);
