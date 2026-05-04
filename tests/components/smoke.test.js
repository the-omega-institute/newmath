import { describe, it, expect } from 'vitest';

describe('vitest infrastructure', () => {
  it('runs a trivial test', () => {
    expect(1 + 1).toBe(2);
  });

  it('has jsdom DOM globals available', () => {
    const div = document.createElement('div');
    div.textContent = 'hello';
    expect(div.textContent).toBe('hello');
  });
});
