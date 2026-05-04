/**
 * error-states.js — Friendly error UI fallbacks for dossier failures.
 *
 * Renders and displays error states for:
 *   - theorem-not-found: URL ?theorem=foo but graph has no record
 *   - dependency-cycle: closure traversal hit a cycle
 *   - katex-render-failure: KaTeX failed to render a statement
 *   - paper-marker-missing: paper_marker_sites entry has no resolvable anchor
 *   - github-permalink-404: GitHub blob URL returns 404
 *
 * No third-party deps. ES module, named exports only.
 */

/**
 * Escape HTML special characters in user-controlled strings.
 * @param {string} str
 * @returns {string}
 */
function escapeHtml(str) {
  const map = {
    '&': '&amp;',
    '<': '&lt;',
    '>': '&gt;',
    '"': '&quot;',
    "'": '&#39;',
  };
  return String(str).replace(/[&<>"']/g, (ch) => map[ch]);
}

/**
 * Render an error state as HTML string.
 *
 * @param {string} kind - One of: "theorem-not-found", "dependency-cycle",
 *   "katex-render-failure", "paper-marker-missing", "github-permalink-404"
 * @param {Object} args - kind-specific arguments:
 *   - theorem-not-found: {wanted: string, suggestions: string[]}
 *   - dependency-cycle: {recordName: string, cycleHint?: string}
 *   - katex-render-failure: {raw: string, error?: string}
 *   - paper-marker-missing: {recordName: string, expectedSite: string}
 *   - github-permalink-404: {url: string}
 * @returns {string} HTML string
 */
export function renderError(kind, args = {}) {
  switch (kind) {
    case 'theorem-not-found': {
      const wanted = escapeHtml(args.wanted || '');
      const suggestions = (args.suggestions || []).slice(0, 5);
      const suggestionHtml = suggestions.length
        ? suggestions
            .map((s) => `<code>${escapeHtml(s)}</code>`)
            .join(', ')
        : '(no suggestions)';
      return `<div class="error-state" style="font-family: monospace; color: #333; line-height: 1.5; padding: 1em;">
  <strong>no such theorem</strong> <code>${wanted}</code>.
  <br/>did you mean: ${suggestionHtml}
</div>`;
    }

    case 'dependency-cycle': {
      const recordName = escapeHtml(args.recordName || 'unknown');
      return `<div class="error-state" style="font-family: monospace; color: #333; line-height: 1.5; padding: 1em;">
  <strong>dependency cycle detected</strong> reaching <code>${recordName}</code>.
  <br/>transit map traversal halted at this node — non-cyclic upstream still renders.
</div>`;
    }

    case 'katex-render-failure': {
      const raw = escapeHtml(args.raw || '');
      return `<div class="error-state" style="font-family: monospace; color: #666; line-height: 1.5; padding: 1em;">
  <code title="KaTeX render failed; showing raw lean">${raw}</code>
</div>`;
    }

    case 'paper-marker-missing': {
      const recordName = escapeHtml(args.recordName || 'unknown');
      const expectedSite = escapeHtml(args.expectedSite || 'unknown');
      return `<div class="error-state" style="font-family: monospace; color: #333; line-height: 1.5; padding: 1em;">
  <strong>paper marker for</strong> <code>${recordName}</code> (<code>${expectedSite}</code>) <strong>has no resolvable anchor</strong> — PDF link unavailable for this site.
</div>`;
    }

    case 'github-permalink-404': {
      const url = escapeHtml(args.url || '');
      return `<div class="error-state" style="font-family: monospace; color: #333; line-height: 1.5; padding: 1em;">
  <strong>GitHub permalink may be stale:</strong> <code>${url}</code> returned 404.
  <br/>The theorem still exists; the SHA may have rotated. Re-deploy the dossier to refresh.
</div>`;
    }

    default: {
      return `<div class="error-state" style="font-family: monospace; color: #666; line-height: 1.5; padding: 1em;">
  <strong>error:</strong> unknown kind "${escapeHtml(kind)}". Check browser console for details.
</div>`;
    }
  }
}

/**
 * Render the error and attach to the given DOM container (clears existing content).
 *
 * @param {HTMLElement} container
 * @param {string} kind
 * @param {Object} args
 */
export function showError(container, kind, args = {}) {
  if (!container) return;
  container.innerHTML = renderError(kind, args);
}
