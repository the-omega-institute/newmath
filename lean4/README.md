# BEDC Lean mirror

This `lean4/` tree is the Phase 1 mirror-port scaffold for BEDC.

- Toolchain: `leanprover/lean4:v4.28.0`
- Dependency policy: mathlib-free by design
- Verification status: `BEDC/BaseReflection.lean` preserves three real proofs from the source scaffold; the FKernel modules are statement skeletons with `sorry`

To build locally after all lanes finish:

```sh
cd lean4
lake build
```
