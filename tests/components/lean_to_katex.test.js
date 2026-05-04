import { describe, it, expect } from 'vitest';
import { renderStatement } from '../../docs/dossier/components/lean_to_katex.js';

const GLOSSARY = {
  "Cont": {"pattern": "Cont $a $f $b", "katex": "$a \\xrightarrow{$f} $b"},
  "BHist.Empty": {"pattern": "BHist.Empty", "katex": "\\varepsilon"},
  "psame": {"pattern": "psame $X $Y", "katex": "$X \\simeq_p $Y"},
  "Nat": {"pattern": "Nat", "katex": "\\mathbb{N}"},
  "Prod": {"pattern": "Prod $a $b", "katex": "$a \\times $b"},
};

describe('lean_to_katex', () => {
  it('tier 1: renders glossary pattern', () => {
    const r = renderStatement('Cont a f b', GLOSSARY);
    expect(r.tier).toBe(1);
    expect(r.html).toContain('xrightarrow');
  });

  it('tier 2: translates ∀ → \\forall', () => {
    const r = renderStatement('∀ a, P a', GLOSSARY);
    expect(r.tier).toBe(2);
    expect(r.html).toContain('\\forall');
  });

  it('tier 3: monospace fallback for unknown', () => {
    const r = renderStatement('SomethingNotInGlossary qwerty asdfgh', GLOSSARY);
    expect(r.tier).toBe(3);
    expect(r.html).toContain('<code>');
  });

  it('tier 1 with recursive arg: Cont a Cont x g y b', () => {
    const r = renderStatement('Cont a Cont x g y b', GLOSSARY);
    // The inner Cont should be recursively rendered, wrapped in {}
    expect(r.html).toMatch(/\{[^}]*xrightarrow[^}]*\}/);
    expect(r.tier).toBe(1);
  });

  it('depth cap prevents stack blowup', () => {
    // Adversarial: deeply nested Cont chains
    const adversarial = Array(20).fill('Cont a f b').join(' Cont ');
    expect(() => renderStatement(adversarial, GLOSSARY)).not.toThrow();
  });

  it('theorem-level tier = MIN over tokens', () => {
    // Cont a f b is tier 1; ZzzzNotKnown is tier 3 → result tier 3
    const r = renderStatement('Cont a f b ZzzzNotKnown qwerty asdf', GLOSSARY);
    expect(r.tier).toBe(3);
  });

  it('empty input returns tier 3 with empty html', () => {
    const r = renderStatement('', GLOSSARY);
    expect(r.tier).toBe(3);
    expect(r.html).toBe('<code></code>');
  });

  it('escapes HTML in tier 3 fallback', () => {
    const r = renderStatement('<script>alert(1)</script>', GLOSSARY);
    expect(r.html).not.toContain('<script>');
    expect(r.html).toContain('&lt;script&gt;');
  });

  it('zero-arg pattern: BHist.Empty renders to \\varepsilon', () => {
    const r = renderStatement('BHist.Empty', GLOSSARY);
    expect(r.tier).toBe(1);
    expect(r.html).toContain('varepsilon');
  });

  it('tier 2: ASCII forall keyword', () => {
    const r = renderStatement('forall n, n > 0', GLOSSARY);
    expect(r.tier).toBe(2);
    expect(r.html).toContain('\\forall');
  });

  it('tier 2: logical connectives ∧ ∨ ¬', () => {
    const r = renderStatement('P ∧ Q ∨ ¬ R', GLOSSARY);
    expect(r.tier).toBe(2);
    expect(r.html).toContain('\\land');
    expect(r.html).toContain('\\lor');
    expect(r.html).toContain('\\neg');
  });

  it('Prod renders as product type', () => {
    const r = renderStatement('Prod Nat Nat', GLOSSARY);
    expect(r.tier).toBe(1);
    expect(r.html).toContain('times');
  });

  it('psame renders with simeq', () => {
    const r = renderStatement('psame A B', GLOSSARY);
    expect(r.tier).toBe(1);
    expect(r.html).toContain('simeq_p');
  });
});
