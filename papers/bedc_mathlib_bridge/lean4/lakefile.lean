import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"
require BEDC from "../../../lean4"

package "bedc_mathlib_bridge" where
  leanOptions := #[⟨`maxHeartbeats, 400000⟩]

@[default_target]
lean_lib BedcMathlibBridge where
