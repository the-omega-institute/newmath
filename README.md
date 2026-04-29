# newmath — BEDC Active Theory Repository

`newmath` is the active theory repository for the Binary Emission Discovery Calculus (BEDC), combining a Lean 4 formalization with a LaTeX paper track.

The repository is mathlib-free by design. Formalization starts from first principles rather than importing Mathlib as a proof substrate.

## Repository Layout

- `papers/bedc/` — LaTeX manuscript for BEDC
- `lean4/` — Lean 4 formalization
- `tools/` — auxiliary scripts and audit helpers when present

## Build

```bash
cd lean4 && lake build
cd papers/bedc && make
```

## Status

v0.1 is a mirror-port phase for the BEDC v1.5.5 manuscript. Planned follow-up phases target v0.2 normalization and v0.3 post-migration cleanup.

## License

GPOL

## Reference

Chinese version: [README.zh-CN.md](README.zh-CN.md)
