// Vitest configuration for BEDC dossier component tests.
// Tests live under tests/components/ and exercise the JS modules in
// docs/dossier/components/ (loaded via Quarto resources at deploy time).
import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: {
    environment: 'jsdom',
    include: ['tests/components/**/*.test.js'],
    globals: false,
  },
});
