import Lake

open Lake DSL

package rule110_cross_check where
  keywords := #["bedc", "rule110", "cross-check"]

require BEDC from "../../lean4"

lean_lib Rule110CrossCheck where

@[default_target]
lean_exe «rule110-cross-check» where
  root := `Rule110CrossCheck
  supportInterpreter := true
