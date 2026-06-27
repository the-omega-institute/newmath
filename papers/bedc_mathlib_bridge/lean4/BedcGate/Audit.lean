import Lean
import Lean.Meta.Instances
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import BedcGate.Provenance

open Lean
open Lean.Meta
open Lean.Elab.Command

namespace BedcGate

structure Policy where
  bridgeDeclPrefix : Name
  bridgeModulePrefix : Name
  bedcDeclPrefix : Name
  bedcModulePrefix : Name
  trackedTypeHeads : Array Name
  operationClasses : Array Name
  allowedPrimitivePrefixes : Array Name := #[]
  provenanceCutpoints : Array Name := #[]
  ignoredDeclPrefixes : Array Name := #[]
  transportDenylist : Array Name := #[]

def formatNames (names : Array Name) : String :=
  String.intercalate ", " (names.toList.map Name.toString)

def matchesNamePrefix (pfx n : Name) : Bool :=
  pfx == n || pfx.isPrefixOf n

partial def hasGeneratedComponent : Name -> Bool
  | Name.anonymous => false
  | Name.str parent component =>
      component.startsWith "_" ||
        component.startsWith "match_" ||
        component.startsWith "proof_" ||
        hasGeneratedComponent parent
  | Name.num parent _ => hasGeneratedComponent parent

def hasStructureAuxSuffix : Name -> Bool
  | .str (.str _ "mk") "injEq" => true
  | .str _ "noConfusion" => true
  | .str _ "noConfusionType" => true
  | .str _ "rec" => true
  | .str _ "recOn" => true
  | .str _ "casesOn" => true
  | _ => false

def shouldAuditPublicName (name : Name) : Bool :=
  !name.isInternal &&
    !name.hasMacroScopes &&
    !hasGeneratedComponent name &&
    !hasStructureAuxSuffix name

def moduleOf? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

def isFromModulePrefix (env : Environment) (modulePrefix n : Name) : Bool :=
  match moduleOf? env n with
  | some modName => modulePrefix.isPrefixOf modName
  | none => false

def isBridgeDecl (p : Policy) (env : Environment) (n : Name) : Bool :=
  !p.ignoredDeclPrefixes.any (fun pfx => pfx.isPrefixOf n) &&
    (p.bridgeDeclPrefix.isPrefixOf n ||
      isFromModulePrefix env p.bridgeModulePrefix n)

def isBedcPrimitive (p : Policy) (env : Environment) (n : Name) : Bool :=
  p.bedcDeclPrefix.isPrefixOf n &&
    isFromModulePrefix env p.bedcModulePrefix n

def bridgeDecls (p : Policy) (env : Environment) :
    Array (Name × ConstantInfo) := Id.run do
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    if shouldAuditPublicName n && isBridgeDecl p env n then
      out := out.push (n, ci)
  return out.qsort fun a b => Name.quickLt a.1 b.1

def auditGateA (p : Policy) : CommandElabM Nat := do
  let env ← getEnv
  let mut audited : Nat := 0
  for (n, _) in bridgeDecls p env do
    audited := audited + 1
    let axioms ← collectAxioms n
    unless axioms.isEmpty do
      throwError m!
        "BEDC_GATE_A_AXIOM: bridge declaration `{n}` depends on axiom(s): \
        {formatNames (axioms.qsort Name.quickLt)}"
  return audited

private def instanceTarget? (ci : ConstantInfo) : MetaM (Option (Name × NameSet)) := do
  forallTelescopeReducing ci.type fun _ result => do
    let result ← whnf result
    match result.getAppFn with
    | .const cls _ => pure <| some (cls, result.getUsedConstantsAsSet)
    | _ => pure none

private def auditDerivedDecl
    (p : Policy) (env : Environment) (n primitive : Name) : CommandElabM Unit := do
  unless isBedcPrimitive p env primitive do
    unless p.allowedPrimitivePrefixes.any (fun pfx => pfx.isPrefixOf primitive) do
      throwError m!
        "BEDC_GATE_B_FOREIGN_PRIMITIVE: `{n}` names `{primitive}`, \
        but that declaration is not owned by the configured BEDC modules"
  let deps := ValueDeps.collect env n p.provenanceCutpoints
  unless deps.contains primitive do
    throwError m!
      "BEDC_GATE_B_MISSING_DEP: `{n}` claims `{primitive}`, \
      but it is not reachable without crossing a provenance cutpoint"

def auditGateB (p : Policy) : CommandElabM Nat := do
  let env ← getEnv
  let mut audited : Nat := 0
  for (n, ci) in bridgeDecls p env do
    let attr? := bedcDerivedAttr.getParam? env n
    if let some primitive := attr? then
      audited := audited + 1
      auditDerivedDecl p env n primitive
    if Meta.isInstanceCore env n then
      let target? ← liftTermElabM <| instanceTarget? ci
      match target? with
      | none => pure ()
      | some (cls, targetConsts) =>
          let relevant :=
            p.operationClasses.contains cls &&
              p.trackedTypeHeads.any fun t => targetConsts.contains t
          if relevant && attr?.isNone then
            throwError m!
              "BEDC_GATE_B_MISSING_ATTR: operation instance `{n}` has class `{cls}` \
              on a tracked BEDC carrier, but has no `@[bedcDerived ...]` annotation"
          if relevant then
            let deps := ValueDeps.collect env n p.provenanceCutpoints
            let depArray := deps.toArray
            let hits := p.transportDenylist.filter fun denied =>
              depArray.any (fun dep => matchesNamePrefix denied dep)
            unless hits.isEmpty do
              throwError m!
                "BEDC_GATE_B_TRANSPORT: operation instance `{n}` depends on \
                denied transport/classical declaration(s): {formatNames hits}"
  return audited

def audit (p : Policy) : CommandElabM Unit := do
  let gateACount ← auditGateA p
  let gateBCount ← auditGateB p
  logInfo m!"[bedc-gate] Gate A audited {gateACount}; Gate B audited {gateBCount}"

end BedcGate
