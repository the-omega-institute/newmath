import Lake
open Lake DSL

package "BEDC" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`maxHeartbeats, 400000⟩
  ]

@[default_target]
lean_lib «BEDC» where
  -- add any library configuration options here

lean_exe "rule110-cross-check" where
  root := `scripts.rule110_cross_check
