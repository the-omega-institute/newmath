import Lean
import Lean.Util.FoldConsts

open Lean

namespace BedcGate

namespace ValueDeps

structure State where
  seen : NameSet := {}

abbrev M := ReaderT Environment (StateM State)

/--
Collect transitive value dependencies. The traversal follows only definition
and opaque-definition values. The declaration type and theorem proof bodies are
not expanded. Cutpoints are recorded as leaves.
-/
partial def visit (cutpoints : Array Name) (n : Name) : M Unit := do
  if (← get).seen.contains n then
    return
  modify fun s => { s with seen := s.seen.insert n }
  if cutpoints.contains n then
    return
  let env ← read
  let follow (e : Expr) : M Unit := do
    for c in e.getUsedConstants do
      visit cutpoints c
  match env.find? n with
  | some (.defnInfo v) => follow v.value
  | some (.opaqueInfo v) => follow v.value
  | _ => pure ()

def collect (env : Environment) (root : Name) (cutpoints : Array Name := #[]) :
    NameSet :=
  let (_, st) := ((visit cutpoints root).run env).run {}
  st.seen

end ValueDeps

initialize bedcDerivedAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `bedcDerived
    descr :=
      "BEDC primitive that must occur in the declaration's transitive value dependencies"
    getParam := fun decl stx => do
      let ident ← Attribute.Builtin.getIdent stx
      let primitive ←
        try
          resolveGlobalConstNoOverload ident
        catch _ =>
          throwError m!
            "BEDC_GATE_B_FOREIGN_PRIMITIVE: `{decl}` names unresolved primitive `{ident}`"
      let env ← getEnv
      let deps := ValueDeps.collect env decl
      unless deps.contains primitive do
        throwError m!
          "BEDC_GATE_B_MISSING_DEP: `{decl}` is annotated with `{primitive}`, \
          but the primitive is not reachable from its value"
      pure primitive
  }

end BedcGate
