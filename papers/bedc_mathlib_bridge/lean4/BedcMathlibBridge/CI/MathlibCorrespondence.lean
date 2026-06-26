import BedcMathlibBridge.All
import Lean
import Lean.Util.CollectAxioms

namespace BedcMathlibBridge.CI.MathlibCorrespondence

open Lean
open Lean.Elab.Command

structure CorrespondenceExpectation where
  rowId : String
  correspondenceDecl : Name
  bedcDecl : Name
  mathlibDecl : Name

def formatNames (names : Array Name) : String :=
  String.intercalate ", " (names.toList.map Name.toString)

def containsName (xs : Array Name) (x : Name) : Bool :=
  xs.any fun y => y == x

def matchesPrefix (pfx candidate : Name) : Bool :=
  pfx == candidate || pfx.isPrefixOf candidate

def containsPrefix (xs : Array Name) (pfx : Name) : Bool :=
  xs.any fun x => matchesPrefix pfx x

def containsAnyPrefix (xs prefixes : Array Name) : Bool :=
  prefixes.any fun pfx => containsPrefix xs pfx

def bedcPrefixes (bedcDecl : Name) : Array Name :=
  #[
    bedcDecl,
    `BEDC,
    `BedcMathlibBridge.Constructive,
    `BedcMathlibBridge.Core,
    `BedcMathlibBridge.Adapter
  ]

def trivialResultHeads : Array Name := #[
  ``True,
  ``Unit,
  ``PUnit,
  ``Empty,
  ``False
]

def typeResultHead? (ci : ConstantInfo) : CommandElabM (Option Name) := do
  liftTermElabM <| Meta.forallTelescopeReducing ci.type fun _ result => do
    let result ← Meta.whnf result
    match result.getAppFn with
    | .const n _ => pure (some n)
    | _ => pure none

def auditOne (e : CorrespondenceExpectation) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains e.bedcDecl do
    throwError m!
      "BEDC_GATE_W_NO_MATHLIB_CORRESPONDENCE: row `{e.rowId}` names absent \
      BEDC-side declaration `{e.bedcDecl}`"
  unless env.contains e.mathlibDecl do
    throwError m!
      "BEDC_GATE_W_NO_MATHLIB_CORRESPONDENCE: row `{e.rowId}` names absent \
      mathlib-side declaration `{e.mathlibDecl}`"
  let some ci := env.find? e.correspondenceDecl
    | throwError m!
        "BEDC_GATE_W_NO_MATHLIB_CORRESPONDENCE: row `{e.rowId}` names absent \
        correspondence declaration `{e.correspondenceDecl}`"
  let axioms ← collectAxioms e.correspondenceDecl
  unless axioms.isEmpty do
    throwError m!
      "BEDC_GATE_W_NO_MATHLIB_CORRESPONDENCE: row `{e.rowId}` correspondence \
      `{e.correspondenceDecl}` depends on axiom(s): {formatNames (axioms.qsort Name.quickLt)}"
  let head? ← typeResultHead? ci
  if head?.any (fun head => containsName trivialResultHeads head) then
    throwError m!
      "BEDC_GATE_W_NO_MATHLIB_CORRESPONDENCE: row `{e.rowId}` correspondence \
      `{e.correspondenceDecl}` has trivial result head {head?}"
  let constants := ci.type.getUsedConstants
  unless containsAnyPrefix constants (bedcPrefixes e.bedcDecl) do
    throwError m!
      "BEDC_GATE_W_NO_MATHLIB_CORRESPONDENCE: row `{e.rowId}` correspondence \
      `{e.correspondenceDecl}` type does not reference BEDC-side anchor `{e.bedcDecl}`"
  unless containsPrefix constants e.mathlibDecl do
    throwError m!
      "BEDC_GATE_W_NO_MATHLIB_CORRESPONDENCE: row `{e.rowId}` correspondence \
      `{e.correspondenceDecl}` type does not reference mathlib-side anchor `{e.mathlibDecl}`"

def audit (expected : Array CorrespondenceExpectation) : CommandElabM Unit := do
  for e in expected do
    auditOne e
  logInfo m!"[mathlib-correspondence] audited {expected.size} exported_core row(s)"

end BedcMathlibBridge.CI.MathlibCorrespondence
