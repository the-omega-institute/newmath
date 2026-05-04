/**
 * search.js — Pure substring + region-prefix search over theorem_search_index.json.
 *
 * No DOM access. No third-party deps. ES module, named export only.
 *
 * Tier order (lower = higher priority):
 *   1  exact full-name match
 *   2  region prefix match  (query matches start of record.region)
 *   3  substring in name    (case-insensitive)
 *   4  substring in region  (case-insensitive)
 *
 * Within each tier, records are sorted alphabetically by name.
 * Empty / whitespace query → {ranked: [], total: 0}.
 * Single-character query caps returned results at 10 regardless of opts.limit.
 */

/**
 * @param {string} query
 * @param {Array<{name: string, region: string, status: string}>} index
 * @param {{ limit?: number }} [opts]
 * @returns {{ ranked: Array, total: number }}
 */
export function searchIndex(query, index, opts = {}) {
  const raw = typeof query === "string" ? query.trim() : "";
  if (!raw) return { ranked: [], total: 0 };

  const q = raw.toLowerCase();
  const isSingleChar = q.length === 1;
  const limit = isSingleChar ? 10 : (opts.limit != null ? opts.limit : 50);

  const tier1 = [];
  const tier2 = [];
  const tier3 = [];
  const tier4 = [];

  for (const rec of index) {
    const nameLower   = rec.name.toLowerCase();
    const regionLower = rec.region.toLowerCase();

    if (rec.name === raw) {
      tier1.push(rec);
    } else if (regionLower.startsWith(q)) {
      tier2.push(rec);
    } else if (nameLower.includes(q)) {
      tier3.push(rec);
    } else if (regionLower.includes(q)) {
      tier4.push(rec);
    }
  }

  const byName = (a, b) => a.name < b.name ? -1 : a.name > b.name ? 1 : 0;
  tier1.sort(byName);
  tier2.sort(byName);
  tier3.sort(byName);
  tier4.sort(byName);

  const all = [...tier1, ...tier2, ...tier3, ...tier4];
  const total = all.length;
  const ranked = all.slice(0, limit);

  return { ranked, total };
}
