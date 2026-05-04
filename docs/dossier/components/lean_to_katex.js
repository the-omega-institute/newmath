/**
 * lean_to_katex.js — 3-tier KaTeX statement renderer.
 *
 * Translates Lean-style statement text into KaTeX-renderable HTML.
 * No runtime dependencies. Glossary is passed by the caller (no async init).
 *
 * Tier 1: every token in the statement matched a glossary pattern
 * Tier 2: at least one structural Unicode/binder translation fired, no tier-1 miss
 *         (or: structural pass fires over a mix of tier-1 hits and plain tokens)
 * Tier 3: no glossary match AND no structural translation → monospace fallback
 *
 * Theorem-level tier = MIN over segments for tier 1 vs non-tier-1;
 * structural pass is applied statement-wide to determine tier 2 vs tier 3.
 */

/**
 * Escape HTML special characters: <, >, &, ", '
 */
function escapeHtml(text) {
  return String(text)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

/**
 * Parse a glossary pattern string into {base, vars}.
 * e.g. "Cont $a $f $b" → {base: "Cont", vars: ["$a","$f","$b"]}
 */
function parsePattern(pattern) {
  const parts = pattern.trim().split(/\s+/);
  return { base: parts[0], vars: parts.slice(1).filter(p => p.startsWith('$')) };
}

/**
 * Tier 1 pattern lookup with recursive substitution.
 *
 * Tries to match a glossary entry starting at tokens[startIdx].
 * Returns {katex: string, consumed: number} or null.
 *
 * @param {string[]} tokens
 * @param {number}   startIdx
 * @param {Object}   glossary
 * @param {number}   depth      current recursion depth
 * @param {number}   depthCap   max recursion depth before fallback
 */
function tryTier1(tokens, startIdx, glossary, depth, depthCap) {
  if (depth >= depthCap) return null;
  if (startIdx >= tokens.length) return null;

  const base = tokens[startIdx];
  const entry = glossary[base];
  if (!entry) return null;

  const { vars } = parsePattern(entry.pattern);
  const argCount = vars.length;

  if (argCount === 0) {
    return { katex: entry.katex, consumed: 1 };
  }

  // We need at least argCount tokens after the base
  if (startIdx + argCount >= tokens.length) return null;

  const substituted = {};
  let cursor = startIdx + 1;

  for (let i = 0; i < argCount; i++) {
    const varName = vars[i];
    const sub = tryTier1(tokens, cursor, glossary, depth + 1, depthCap);
    if (sub !== null) {
      substituted[varName] = `{${sub.katex}}`;
      cursor += sub.consumed;
    } else {
      if (cursor >= tokens.length) return null;
      substituted[varName] = tokens[cursor];
      cursor += 1;
    }
  }

  // Substitute $var placeholders in the katex template.
  // Sort by descending length to avoid "$a" matching inside "$ab".
  let result = entry.katex;
  const sortedVars = Object.keys(substituted).sort((a, b) => b.length - a.length);
  for (const varName of sortedVars) {
    result = result.split(varName).join(substituted[varName]);
  }

  return { katex: result, consumed: cursor - startIdx };
}

/**
 * Tier 2 structural translation table.
 * Applied statement-wide to raw text (not per token).
 * Returns {katex: string, fired: boolean}.
 */
const STRUCTURAL_RULES = [
  [/∀/g,        '\\forall '],
  [/∃/g,        '\\exists '],
  [/→/g,        '\\to '],
  [/↔/g,        '\\leftrightarrow '],
  [/∧/g,        '\\land '],
  [/∨/g,        '\\lor '],
  [/¬/g,        '\\neg '],
  [/λ/g,        '\\lambda '],
  [/α/g,        '\\alpha '],
  [/β/g,        '\\beta '],
  [/γ/g,        '\\gamma '],
  [/δ/g,        '\\delta '],
  [/ε/g,        '\\varepsilon '],
  [/≤/g,        '\\leq '],
  [/≥/g,        '\\geq '],
  [/≠/g,        '\\neq '],
  [/≡/g,        '\\equiv '],
  [/⟹/g,       '\\Rightarrow '],
  [/⊢/g,        '\\vdash '],
  [/∈/g,        '\\in '],
  [/∉/g,        '\\notin '],
  [/⊆/g,        '\\subseteq '],
  [/∩/g,        '\\cap '],
  [/∪/g,        '\\cup '],
  [/∅/g,        '\\emptyset '],
  [/\bforall\b/g, '\\forall '],
  [/\bexists\b/g, '\\exists '],
  [/ : /g,      ' \\,:\\, '],
];

function applyStructural(text) {
  let result = text;
  let fired = false;
  for (const [regex, replacement] of STRUCTURAL_RULES) {
    const next = result.replace(regex, replacement);
    if (next !== result) {
      fired = true;
      result = next;
    }
  }
  return { katex: result, fired };
}

/**
 * Tier 3 monospace fallback.
 */
function tier3Fallback(text) {
  return `<code>${escapeHtml(text)}</code>`;
}

/**
 * Render a Lean statement string as HTML.
 *
 * Returns {html: string, tier: 1|2|3}.
 *   tier 1: all segments were tier-1 glossary hits
 *   tier 2: at least one structural translation fired (and no fully-unrenderable miss
 *           forces tier 3) — OR a mix where structural fills the gaps
 *   tier 3: no glossary hit AND no structural translation anywhere
 *
 * Theorem-level tier determination:
 *   - Walk tokens greedily with tryTier1.
 *   - Track whether any token was a tier-1 hit (allTier1 flag).
 *   - After the token walk, apply structural pass over the combined raw-fallback text.
 *   - If allTier1 → tier 1.
 *   - Else if structural fired anywhere → tier 2.
 *   - Else → tier 3.
 *
 * The MIN-over-tokens rule applies for tier 1 vs tier 3:
 *   if any token is NOT a tier-1 hit AND structural doesn't rescue the statement,
 *   the result is tier 3 (honest worst-case).
 *
 * @param {string} statement
 * @param {Object} glossary    {key: {pattern: string, katex: string}}
 * @param {Object} [opts]
 * @param {number} [opts.depthCap=4]
 */
export function renderStatement(statement, glossary, opts = {}) {
  const depthCap = (opts.depthCap !== undefined) ? opts.depthCap : 4;

  if (!statement || statement.trim() === '') {
    return { html: tier3Fallback(''), tier: 3 };
  }

  const tokens = statement.trim().split(/\s+/);
  const segments = [];   // {katex: string, isTier1: boolean}[]
  let cursor = 0;

  while (cursor < tokens.length) {
    const match = tryTier1(tokens, cursor, glossary, 0, depthCap);
    if (match !== null) {
      segments.push({ katex: match.katex, isTier1: true });
      cursor += match.consumed;
    } else {
      segments.push({ katex: tokens[cursor], isTier1: false });
      cursor += 1;
    }
  }

  const allTier1 = segments.every(s => s.isTier1);

  if (allTier1) {
    const combined = segments.map(s => s.katex).join(' ');
    return {
      html: `<span class="katex-inline">${escapeHtml(combined)}</span>`,
      tier: 1,
    };
  }

  // Not all tier 1: collect the raw (non-tier-1) text and apply structural pass
  // over the entire original statement to check for Unicode/binder hits.
  const { katex: structKatex, fired } = applyStructural(statement.trim());

  if (fired) {
    // Tier 2: build output by applying structural pass to each non-tier-1 segment,
    // keeping tier-1 segments as-is.
    const parts = segments.map(s => {
      if (s.isTier1) return s.katex;
      const { katex } = applyStructural(s.katex);
      return katex;
    });
    const combined = parts.join(' ');
    return {
      html: `<span class="katex-inline">${escapeHtml(combined)}</span>`,
      tier: 2,
    };
  }

  // Tier 3: no glossary hits, no structural translations.
  // Per MIN-over-tokens: the whole statement falls back to monospace.
  // If there were some tier-1 hits mixed with tier-3 misses, the worst-case tier is 3.
  return {
    html: tier3Fallback(statement.trim()),
    tier: 3,
  };
}

/**
 * Load glossary from a JSON URL.
 * Returns Promise<Object>.
 */
export async function loadGlossary(url) {
  const res = await fetch(url);
  if (!res.ok) throw new Error(`Failed to load glossary: ${res.status} ${url}`);
  return res.json();
}
