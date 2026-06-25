import BedcMathlibBridge.All
import BedcGate.Audit

namespace BedcMathlibBridge.Audit.ThinLayerGuard

open Lean
open Lean.Elab.Command

def auditedModulePrefixes : Array Name := #[
  `BedcMathlibBridge.Constructive,
  `BedcMathlibBridge.Export,
  `BedcMathlibBridge.Core,
  `BedcMathlibBridge.Adapter
]

def ignoredDeclPrefixes : Array Name := #[
  `BedcGate,
  `BedcMathlibBridge.CI,
  `BedcMathlibBridge.Audit,
  -- Bridge correspondence infrastructure lives on the bridge side even when
  -- its carrier/relation shape is mathlib-free.
  `BedcMathlibBridge.RelEquiv,
  `BedcMathlibBridge.RelQuotEquiv,
  -- Bool is a bridge canary for the thin-layer audit; its BEDC-side readback
  -- facts are present under BEDC.Derived.BoolUp and can be wired separately.
  `BedcMathlibBridge.Constructive.Bool
]

def formatNames (names : Array Name) : String :=
  String.intercalate ", " (names.toList.map Name.toString)

def matchesAnyPrefix (prefixes : Array Name) (n : Name) : Bool :=
  prefixes.any fun pfx => pfx == n || pfx.isPrefixOf n

def isProvenanceAnchor (n : Name) : Bool :=
  n.toString.contains "ProvenanceAnchor"

def isStructureAuxDecl (n : Name) : Bool :=
  match n with
  | .str _ "ctorIdx" => true
  | .str _ "mk" => true
  | .str (.str _ "mk") "inj" => true
  | .str (.str _ "mk") "injEq" => true
  | .str (.str _ "mk") "sizeOf_spec" => true
  | .str _ "noConfusion" => true
  | .str _ "noConfusionType" => true
  | .str _ "rec" => true
  | .str _ "recOn" => true
  | .str _ "casesOn" => true
  | _ => false

def shouldIgnoreDecl (n : Name) : Bool :=
  matchesAnyPrefix ignoredDeclPrefixes n || isProvenanceAnchor n || isStructureAuxDecl n

def isAuditedContentDecl (env : Environment) (n : Name) : Bool :=
  BedcGate.shouldAuditPublicName n &&
    !shouldIgnoreDecl n &&
    auditedModulePrefixes.any fun pfx => BedcGate.isFromModulePrefix env pfx n

def isRootIntName (n : Name) : Bool :=
  n == `Int || (`Int).isPrefixOf n

def isMathlibDecl (env : Environment) (n : Name) : Bool :=
  BedcGate.isFromModulePrefix env `Mathlib n

def isBridgeJustifyingConstant (env : Environment) (n : Name) : Bool :=
  isRootIntName n || isMathlibDecl env n

def structureProjectionOwner? (env : Environment) (n : Name) : Option Name := Id.run do
  match n with
  | .str structName _ =>
      match Lean.getStructureInfo? env structName with
      | some info =>
          if info.fieldInfo.any (fun field => field.projFn == n) then
            some structName
          else
            none
      | none => none
  | _ => none

def structureInterfaceConstants (env : Environment) (structName : Name) : NameSet :=
  Id.run do
    let mut out := {}
    if let some ci := env.find? structName then
      for c in ci.type.getUsedConstants do
        out := out.insert c
    if let some info := Lean.getStructureInfo? env structName then
      for field in info.fieldInfo do
        if let some ci := env.find? field.projFn then
          for c in ci.type.getUsedConstants do
            out := out.insert c
    return out

def hasBridgeJustifyingStructureInterface
    (env : Environment) (n : Name) : Bool :=
  let structName? :=
    match Lean.getStructureInfo? env n with
    | some _ => some n
    | none => structureProjectionOwner? env n
  match structName? with
  | none => false
  | some structName =>
      (structureInterfaceConstants env structName).toArray.any
        (isBridgeJustifyingConstant env)

def dependencyClosure (env : Environment) (n : Name) (ci : ConstantInfo) : NameSet :=
  Id.run do
    let mut deps := BedcGate.ValueDeps.collect env n
    for c in ci.type.getUsedConstants do
      deps := deps.insert c
      for d in (BedcGate.ValueDeps.collect env c).toArray do
        deps := deps.insert d
    return deps

def hasBridgeJustification (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  (dependencyClosure env n ci).toArray.any (isBridgeJustifyingConstant env) ||
    hasBridgeJustifyingStructureInterface env n

def auditedDecls (env : Environment) : Array (Name × ConstantInfo) := Id.run do
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    if isAuditedContentDecl env n then
      out := out.push (n, ci)
  return out.qsort fun a b => Name.quickLt a.1 b.1

def violationLine (n : Name) : String :=
  s!"BEDC_GATE_THIN_LAYER: `{n}` 是 mathlib-free 数学内容, 属 BEDC core 不属 bridge"

def throwViolations (violations : Array Name) : CommandElabM Unit := do
  unless violations.isEmpty do
    throwError m!"{String.intercalate "\n" (violations.map violationLine).toList}"

def auditSelected (names : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut violations : Array Name := #[]
  for n in names do
    match env.find? n with
    | none => throwError m!"BEDC_GATE_THIN_LAYER_MISSING_DECL: selected declaration `{n}` is absent"
    | some ci =>
        unless hasBridgeJustification env n ci do
          violations := violations.push n
  logInfo m!
    "[thin-layer-selected] audited {names.size} selected declaration(s); \
    {violations.size} violating"
  throwViolations violations

/--
Provenance anchor declarations are intentionally ignored: they exist only to
make dependency registration explicit and are not bridge content.
-/
def audit : CommandElabM Unit := do
  let env ← getEnv
  let decls := auditedDecls env
  let mut violations : Array Name := #[]
  for (n, ci) in decls do
    unless hasBridgeJustification env n ci do
      violations := violations.push n
  logInfo m!
    "[thin-layer] audited {decls.size} bridge content declaration(s); \
    {violations.size} violating"
  throwViolations violations

end BedcMathlibBridge.Audit.ThinLayerGuard
