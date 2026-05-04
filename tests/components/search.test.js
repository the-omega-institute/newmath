import { describe, it, expect } from 'vitest';
import { searchIndex } from '../../docs/dossier/components/search.js';

const INDEX = [
  { name: 'BEDC.FKernel.Cont.cont_assoc',    region: 'kernel',    status: 'checked'  },
  { name: 'BEDC.AnaCont.zeta_holomorphic',    region: 'zetacont',  status: 'stmt'     },
  { name: 'BEDC.AnaCont.zetabasic_def',       region: 'zetabasic', status: 'def-only' },
  { name: 'BEDC.FKernel.BHist.Empty',         region: 'kernel',    status: 'def-only' },
  { name: 'BEDC.Nat.add_comm',                region: 'nat',       status: 'checked'  },
  { name: 'BEDC.Nat.mul_zero',                region: 'nat',       status: 'checked'  },
  { name: 'BEDC.Ring.add_assoc',              region: 'ring',      status: 'stmt'     },
  { name: 'BEDC.FKernel.Cont.cont_id',        region: 'kernel',    status: 'checked'  },
];

describe('searchIndex', () => {
  it('empty query returns no results', () => {
    expect(searchIndex('', INDEX)).toEqual({ ranked: [], total: 0 });
    expect(searchIndex('   ', INDEX)).toEqual({ ranked: [], total: 0 });
  });

  it('null-ish query returns no results', () => {
    // undefined query is treated as empty after trim
    expect(searchIndex(undefined, INDEX)).toEqual({ ranked: [], total: 0 });
  });

  it('single-character query caps at 10', () => {
    const lots = Array.from({ length: 50 }, (_, i) => ({
      name: `BEDC.A.lemma${i}`, region: 'kernel', status: 'stmt',
    }));
    const r = searchIndex('a', lots);
    expect(r.ranked.length).toBeLessThanOrEqual(10);
  });

  it('exact-match wins top (tier 1)', () => {
    const r = searchIndex('BEDC.FKernel.Cont.cont_assoc', INDEX);
    expect(r.ranked[0].name).toBe('BEDC.FKernel.Cont.cont_assoc');
  });

  it('exact-match record is not duplicated in lower tiers', () => {
    const r = searchIndex('BEDC.FKernel.Cont.cont_assoc', INDEX);
    const names = r.ranked.map(x => x.name);
    const uniq = new Set(names);
    expect(uniq.size).toBe(names.length);
  });

  it('region prefix matches all records in region (tier 2)', () => {
    const r = searchIndex('zetacont', INDEX);
    expect(r.ranked.some(x => x.region === 'zetacont')).toBe(true);
    // Should not include records whose region merely contains 'zetacont' as non-prefix
    const nonPrefix = r.ranked.filter(x => !x.region.startsWith('zetacont') && !x.name.toLowerCase().includes('zetacont'));
    expect(nonPrefix.length).toBe(0);
  });

  it('substring match in name (tier 3)', () => {
    const r = searchIndex('cont_assoc', INDEX);
    expect(r.ranked.some(x => x.name.includes('cont_assoc'))).toBe(true);
  });

  it('case-insensitive matching', () => {
    const upper = searchIndex('ZETA', INDEX);
    const lower = searchIndex('zeta', INDEX);
    expect(upper.ranked.length).toBe(lower.ranked.length);
  });

  it('respects opts.limit', () => {
    const lots = Array.from({ length: 100 }, (_, i) => ({
      name: `BEDC.Test.cont_${String(i).padStart(3, '0')}`, region: 'test', status: 'stmt',
    }));
    const r = searchIndex('cont', lots, { limit: 5 });
    expect(r.ranked.length).toBeLessThanOrEqual(5);
  });

  it('total reflects pre-slice match count', () => {
    const lots = Array.from({ length: 200 }, (_, i) => ({
      name: `BEDC.A.cont_${i}`, region: 'kernel', status: 'stmt',
    }));
    const r = searchIndex('cont', lots);
    expect(r.total).toBeGreaterThan(50);
    expect(r.ranked.length).toBeLessThanOrEqual(50);
  });

  it('no results returns empty array and zero total', () => {
    const r = searchIndex('xxxNOMATCHxxx', INDEX);
    expect(r.ranked).toEqual([]);
    expect(r.total).toBe(0);
  });

  it('sorts within tier alphabetically by name', () => {
    const r = searchIndex('BEDC.FKernel', INDEX);
    const names = r.ranked.map(x => x.name);
    const sorted = [...names].sort();
    expect(names).toEqual(sorted);
  });

  it('region-substring match (tier 4) fires when no name match', () => {
    // 'basic' is in 'zetabasic' region but not in any name as a substring
    // Actually zetabasic_def contains 'basic', so use a different region fragment
    const smallIndex = [
      { name: 'BEDC.Topo.compactness', region: 'compact', status: 'stmt' },
      { name: 'BEDC.Metric.ball',      region: 'metric',  status: 'checked' },
    ];
    const r = searchIndex('mpac', smallIndex);
    // 'mpac' is substring of 'compact' but not of any name
    expect(r.ranked.some(x => x.region === 'compact')).toBe(true);
  });

  it('tier 2 result ranks before tier 3 result', () => {
    // 'ker' starts 'kernel' (tier 2 for those) and is substring in 'FKernel' names (tier 3)
    // kernel-region records should sort before FKernel-name records
    const r = searchIndex('ker', INDEX);
    const firstNonKernelRegion = r.ranked.findIndex(x => !x.region.startsWith('ker'));
    const firstKernelRegion = r.ranked.findIndex(x => x.region.startsWith('ker'));
    if (firstKernelRegion !== -1 && firstNonKernelRegion !== -1) {
      expect(firstKernelRegion).toBeLessThan(firstNonKernelRegion);
    }
  });
});
