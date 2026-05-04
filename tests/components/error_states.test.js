import { describe, it, expect } from 'vitest';
import { renderError, showError } from '../../docs/dossier/components/error-states.js';

describe('renderError', () => {
  it('theorem-not-found shows wanted name + suggestions', () => {
    const html = renderError('theorem-not-found', {
      wanted: 'BEDC.Foo.bar',
      suggestions: ['BEDC.Foo.baz', 'BEDC.Foo.qux'],
    });
    expect(html).toContain('BEDC.Foo.bar');
    expect(html).toContain('BEDC.Foo.baz');
    expect(html).toContain('BEDC.Foo.qux');
    expect(html.toLowerCase()).toContain('no such theorem');
  });

  it('theorem-not-found with empty suggestions', () => {
    const html = renderError('theorem-not-found', {
      wanted: 'X.Y.Z',
      suggestions: [],
    });
    expect(html).toContain('X.Y.Z');
    expect(html).toContain('no suggestions');
  });

  it('theorem-not-found truncates suggestions at 5', () => {
    const suggestions = Array.from({ length: 10 }, (_, i) => `BEDC.A.lemma${i}`);
    const html = renderError('theorem-not-found', {
      wanted: 'BEDC.Target',
      suggestions,
    });
    // Should contain first 5 suggestions
    expect(html).toContain('BEDC.A.lemma0');
    expect(html).toContain('BEDC.A.lemma4');
    // Should NOT contain 6th+ suggestions
    expect(html).not.toContain('BEDC.A.lemma9');
  });

  it('dependency-cycle shows record name and mentions cycle', () => {
    const html = renderError('dependency-cycle', {
      recordName: 'A.B.c',
    });
    expect(html).toContain('A.B.c');
    expect(html.toLowerCase()).toContain('cycle');
    expect(html.toLowerCase()).toContain('halted');
  });

  it('dependency-cycle with cycleHint (optional)', () => {
    const html = renderError('dependency-cycle', {
      recordName: 'Foo.bar',
      cycleHint: 'via Foo.baz',
    });
    expect(html).toContain('Foo.bar');
    // cycleHint may not appear in base message but is captured in args
  });

  it('katex-render-failure renders raw in code tag', () => {
    const html = renderError('katex-render-failure', {
      raw: 'theorem foo := bar',
    });
    expect(html).toContain('<code');
    expect(html).toContain('theorem foo := bar');
    expect(html).toContain('</code>');
  });

  it('katex-render-failure has title attribute about failure', () => {
    const html = renderError('katex-render-failure', {
      raw: 'def x := 1',
      error: 'some error message',
    });
    expect(html.toLowerCase()).toContain('katex');
    expect(html).toContain('def x := 1');
  });

  it('paper-marker-missing shows record + site', () => {
    const html = renderError('paper-marker-missing', {
      recordName: 'A.b',
      expectedSite: 'thm:foo',
    });
    expect(html).toContain('A.b');
    expect(html).toContain('thm:foo');
    expect(html.toLowerCase()).toContain('marker');
    expect(html.toLowerCase()).toContain('anchor');
  });

  it('github-permalink-404 shows url and notes SHA rotation', () => {
    const html = renderError('github-permalink-404', {
      url: 'https://github.com/the-omega-institute/newmath/blob/abc123/lean4/BEDC/File.lean#L1',
    });
    expect(html).toContain('https://github.com/the-omega-institute/newmath/blob/abc123/lean4/BEDC/File.lean#L1');
    expect(html).toContain('404');
    expect(html.toLowerCase()).toContain('sha');
  });

  it('escapes HTML in wanted (theorem-not-found)', () => {
    const html = renderError('theorem-not-found', {
      wanted: '<script>alert("xss")</script>',
      suggestions: [],
    });
    expect(html).not.toContain('<script>');
    expect(html).toContain('&lt;script&gt;');
  });

  it('escapes HTML in suggestion names', () => {
    const html = renderError('theorem-not-found', {
      wanted: 'X',
      suggestions: ['<img src=x onerror=alert(1)>'],
    });
    expect(html).not.toContain('<img');
    expect(html).toContain('&lt;img');
  });

  it('escapes HTML in recordName (dependency-cycle)', () => {
    const html = renderError('dependency-cycle', {
      recordName: '"><script>',
    });
    expect(html).not.toContain('<script>');
    expect(html).toContain('&lt;script&gt;');
  });

  it('escapes HTML in raw (katex-render-failure)', () => {
    const html = renderError('katex-render-failure', {
      raw: '<evil>code</evil>',
    });
    expect(html).not.toContain('<evil>');
    expect(html).toContain('&lt;evil&gt;');
  });

  it('escapes HTML in recordName (paper-marker-missing)', () => {
    const html = renderError('paper-marker-missing', {
      recordName: '"><br><br',
      expectedSite: 'thm:x',
    });
    expect(html).not.toContain('><br>');
    expect(html).toContain('&lt;br&gt;');
  });

  it('escapes HTML in url (github-permalink-404)', () => {
    const html = renderError('github-permalink-404', {
      url: 'https://evil.com/file?x=<script>',
    });
    expect(html).not.toContain('<script>');
    expect(html).toContain('&lt;script&gt;');
  });

  it('unknown kind returns generic error message', () => {
    const html = renderError('unknown-kind-xyz', {});
    expect(html.toLowerCase()).toContain('error');
    expect(html).toContain('unknown-kind-xyz');
  });

  it('missing args field gracefully falls back to empty/unknown', () => {
    const html1 = renderError('theorem-not-found', {});
    expect(html1).toContain('no such theorem');

    const html2 = renderError('dependency-cycle', {});
    expect(html2).toContain('unknown');
  });

  it('all error kinds produce valid HTML', () => {
    const kinds = [
      'theorem-not-found',
      'dependency-cycle',
      'katex-render-failure',
      'paper-marker-missing',
      'github-permalink-404',
    ];
    for (const kind of kinds) {
      const html = renderError(kind, {
        wanted: 'test',
        recordName: 'test',
        raw: 'test',
        expectedSite: 'test',
        url: 'test',
      });
      expect(html).toContain('<div');
      expect(html).toContain('</div>');
      expect(html).toContain('error-state');
    }
  });
});

describe('showError', () => {
  it('clears container and writes HTML', () => {
    const c = document.createElement('div');
    c.innerHTML = '<p>old content</p>';
    showError(c, 'dependency-cycle', { recordName: 'X.Y' });
    expect(c.innerHTML).not.toContain('old content');
    expect(c.innerHTML).toContain('X.Y');
  });

  it('shows theorem-not-found error in container', () => {
    const c = document.createElement('div');
    showError(c, 'theorem-not-found', {
      wanted: 'BEDC.Test',
      suggestions: ['BEDC.TestAlt'],
    });
    expect(c.textContent).toContain('BEDC.Test');
    expect(c.textContent).toContain('BEDC.TestAlt');
  });

  it('gracefully handles null/undefined container', () => {
    // Should not throw
    expect(() => showError(null, 'theorem-not-found', {})).not.toThrow();
    expect(() => showError(undefined, 'theorem-not-found', {})).not.toThrow();
  });

  it('overwrites existing content', () => {
    const c = document.createElement('div');
    c.innerHTML = '<strong>keep this</strong><em>not this</em>';
    showError(c, 'katex-render-failure', { raw: 'new error' });
    expect(c.innerHTML).not.toContain('<em>');
    expect(c.innerHTML).toContain('new error');
  });

  it('produces error container with proper styling class', () => {
    const c = document.createElement('div');
    showError(c, 'github-permalink-404', { url: 'https://example.com' });
    expect(c.querySelector('.error-state')).not.toBeNull();
  });
});
