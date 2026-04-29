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
