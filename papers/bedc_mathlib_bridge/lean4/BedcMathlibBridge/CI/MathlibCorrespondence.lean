import BedcMathlibBridge.All
import BedcGate.Provenance
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
  consumedDecls : Array Name

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

def weakConsumedDecls : Array Name := #[
  `BEDC,
  `BedcMathlibBridge.Constructive,
  `BHist,
  `Nat,
  `Int,
  `CInt,
  `BEDC.FKernel.Hist.BHist,
  `BEDC.FKernel.Hist.BHist.Empty,
  `BEDC.FKernel.Hist.bwordLength,
  `BedcMathlibBridge.Constructive.Int.CInt,
  `BedcMathlibBridge.Constructive.Int.CInt.toInt,
  `BedcMathlibBridge.Constructive.Int.CInt.ofInt
]

def weakConsumedTerminal : String -> Bool
  | "BHist" | "Nat" | "Int" | "CInt" | "toInt" | "ofInt" | "toNat" | "ofNat" => true
  | _ => false

def nameTerminal : Name -> String
  | .str _ s => s
  | .num _ n => toString n
  | .anonymous => ""

def consumedDeclAllowed (n : Name) : Bool :=
  (`BEDC).isPrefixOf n || (`BedcMathlibBridge.Constructive).isPrefixOf n

def consumedDeclStrong (n : Name) : Bool :=
  consumedDeclAllowed n && !containsName weakConsumedDecls n && !weakConsumedTerminal (nameTerminal n)

def declarationBodyConstants (ci : ConstantInfo) : Array Name :=
  match ci with
  | .defnInfo v => v.value.getUsedConstants
  | .thmInfo v => v.value.getUsedConstants
  | .opaqueInfo v => v.value.getUsedConstants
  | _ => #[]

def moduleOf? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

def isFromModulePrefix (env : Environment) (modulePrefix n : Name) : Bool :=
  match moduleOf? env n with
  | some modName => modulePrefix.isPrefixOf modName
  | none => false

def shouldExpandValueProof (env : Environment) (n : Name) : Bool :=
  (`BEDC).isPrefixOf n ||
    (`BedcMathlibBridge).isPrefixOf n ||
    isFromModulePrefix env `BEDC n ||
    isFromModulePrefix env `BedcMathlibBridge n

partial def visitValueProof (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then
    return
  modify fun seen => seen.insert n
  unless shouldExpandValueProof env n do
    return
  if let some ci := env.find? n then
    for c in declarationBodyConstants ci do
      visitValueProof env c

def valueProofDeps (env : Environment) (root : Name) : NameSet :=
  Id.run do
    let mut deps := BedcGate.ValueDeps.collect env root
    for d in ((visitValueProof env root).run {} |>.2).toArray do
      deps := deps.insert d
      for e in (BedcGate.ValueDeps.collect env d).toArray do
        deps := deps.insert e
    return deps

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
  if e.consumedDecls.isEmpty then
    throwError m!
      "BEDC_GATE_W_MISSING_VALUE_DEP: row `{e.rowId}` correspondence \
      `{e.correspondenceDecl}` has no registered `bedc_consumed_decl`"
  for consumed in e.consumedDecls do
    unless consumedDeclStrong consumed do
      throwError m!
        "BEDC_GATE_W_WEAK_CONSUMED_DECL: row `{e.rowId}` registered \
        `bedc_consumed_decl` `{consumed}` is too broad to certify correspondence \
        consumption"
    unless env.contains consumed do
      throwError m!
        "BEDC_GATE_W_UNKNOWN_CONSUMED_DECL: row `{e.rowId}` names absent \
        consumed BEDC declaration `{consumed}`"
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
  let deps := valueProofDeps env e.correspondenceDecl
  for consumed in e.consumedDecls do
    unless deps.contains consumed do
      throwError m!
        "BEDC_GATE_W_MISSING_VALUE_DEP: row `{e.rowId}` correspondence \
        `{e.correspondenceDecl}` does not consume `{consumed}` in its value/proof \
        dependency closure"

def audit (expected : Array CorrespondenceExpectation) : CommandElabM Unit := do
  for e in expected do
    auditOne e
  logInfo m!"[mathlib-correspondence] audited {expected.size} exported_core row(s)"

end BedcMathlibBridge.CI.MathlibCorrespondence
