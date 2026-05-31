# newmath — BEDC Active Theory Repository

`newmath` is the active theory repository for the Binary Emission Discovery Calculus (BEDC), combining a Lean 4 formalization with a LaTeX paper track.

The repository is mathlib-free by design. Formalization starts from first principles rather than importing Mathlib as a proof substrate.

## Repository Layout

- `papers/bedc/` — LaTeX manuscript for BEDC
- `lean4/` — Lean 4 formalization
- `tools/` — auxiliary scripts and audit helpers when present

## Build

The operational build and verification contract is maintained in `CLAUDE.md`.
Toolchain and dependency facts are read from the files that drive the build.

```bash
cd lean4 && lake build
cd papers/bedc && make
```

## License

GPOL

## Reference

Chinese version: [README.zh-CN.md](README.zh-CN.md)
