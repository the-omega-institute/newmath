import Lean
import scripts.structural_dna.TestTargets

open Lean
open Lean.Meta

namespace BEDC.StructuralDna

/-!
The structural DNA fingerprint is alpha-equivalence invariant and structurally faithful for
elaborated Lean expressions. Binder display names and metadata are ignored, while constants keep
their canonical names and bound variables keep their de Bruijn indices.

This deliberately does not fold definitional-equality unfolding: `def A := B` and an inline copy of
`B` may receive different fingerprints. Bounded-whnf or unfolding-aware comparison is a separate
extension. Theorem fingerprints ignore proof terms and retain only the proposition shape.

The `reduced_fingerprint` field is separate from the structural fingerprint. It normalizes
definition values through beta, eta, zeta, and transparent constant unfolding, and is used only for
novelty checks that must reject definitional wrappers.
-/

def hashString (s : String) : UInt64 :=
  s.toUTF8.foldl
    (fun acc byte => (acc.xor (UInt64.ofNat byte.toNat)) * 1099511628211)
    14695981039346656037

def hex64 (h : UInt64) : String :=
  let digits := Nat.toDigits 16 h.toNat
  let padding := List.replicate (16 - digits.length) '0'
  String.ofList (padding ++ digits)

def stableHash (s : String) : String :=
  hex64 (hashString s)

def quoteToken (s : String) : String :=
  toString (repr s)

def joinPayload (tag : String) (parts : List String) : String :=
  "(" ++ tag ++ parts.foldl (fun acc part => acc ++ "|" ++ part) "" ++ ")"

def levelPayload (u : Level) (params : List Name) : String :=
  match u with
  | .zero => "(level|zero)"
  | .succ v => joinPayload "level-succ" [levelPayload v params]
  | .max a b => joinPayload "level-max" [levelPayload a params, levelPayload b params]
  | .imax a b => joinPayload "level-imax" [levelPayload a params, levelPayload b params]
  | .param name =>
      let index := params.idxOf name
      if index < params.length then
        joinPayload "level-param" [toString index]
      else
        joinPayload "level-param-free" [quoteToken name.toString]
  | .mvar id => joinPayload "level-mvar" [quoteToken id.name.toString]

def literalPayload : Literal → String
  | .natVal n => joinPayload "lit-nat" [toString n]
  | .strVal s => joinPayload "lit-str" [quoteToken s]

def binderInfoPayload : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

partial def exprPayload (params : List Name) : Expr → String
  | .bvar i => joinPayload "bvar" [toString i]
  | .fvar id => joinPayload "fvar" [quoteToken id.name.toString]
  | .mvar id => joinPayload "mvar" [quoteToken id.name.toString]
  | .sort u => joinPayload "sort" [levelPayload u params]
  | .const name us =>
      joinPayload "const" [
        quoteToken name.toString,
        toString us.length,
        joinPayload "levels" (us.map (levelPayload · params))
      ]
  | .app f a => joinPayload "app" [exprPayload params f, exprPayload params a]
  | .lam _ ty body bi =>
      joinPayload "lam" [binderInfoPayload bi, exprPayload params ty, exprPayload params body]
  | .forallE _ ty body bi =>
      joinPayload "forall" [binderInfoPayload bi, exprPayload params ty, exprPayload params body]
  | .letE _ ty val body _ =>
      joinPayload "let" [
        binderInfoPayload .default,
        exprPayload params ty,
        exprPayload params val,
        exprPayload params body
      ]
  | .lit lit => literalPayload lit
  | .mdata _ e => exprPayload params e
  | .proj structName idx e =>
      joinPayload "proj" [quoteToken structName.toString, toString idx, exprPayload params e]

def exprFingerprint (params : List Name) (e : Expr) : String :=
  stableHash (exprPayload params e)

structure DeclFingerprint where
  fingerprint : String
  typeFp : String
  valueFp : String
  constFp : String
  etaValueFp : String
  reducedFingerprint : String
deriving Repr

structure LambdaBinder where
  binderInfo : String
  typePayload : String
deriving Repr, BEq

structure ClassifierView where
  name : String
  params : List Name
  reducedExpr : Expr
  lambdaBinders : List LambdaBinder
  body : Expr
  bodyFp : String
  fullReducedFp : String
deriving Repr

structure ConjunctLeaf where
  path : String
  expr : Expr
  exprFp : String
  isTrivial : Bool
deriving Repr

partial def collectLams : Expr → Nat × Expr
  | .lam _ _ body _ =>
      let (n, inner) := collectLams body
      (n + 1, inner)
  | .mdata _ e => collectLams e
  | e => (0, e)

partial def appHeadArgs : Expr → Expr × List Expr
  | .app f a =>
      let (head, args) := appHeadArgs f
      (head, args ++ [a])
  | .mdata _ e => appHeadArgs e
  | e => (e, [])

def isEtaArgSequenceFrom : List Expr → Nat → Nat → Bool
  | [], _, idx => idx == 0
  | arg :: rest, arity, idx =>
      arg == Expr.bvar (idx - 1) && isEtaArgSequenceFrom rest arity (idx - 1)

def isEtaArgSequence (args : List Expr) (arity : Nat) : Bool :=
  args.length == arity && isEtaArgSequenceFrom args arity arity

def etaHeadClosedOverRemovedBinders (head : Expr) (arity : Nat) : Bool :=
  !(List.range arity).any (fun i => head.hasLooseBVar i)

def etaReduceValue (e : Expr) : Expr :=
  let (arity, body) := collectLams e
  if arity == 0 then
    e
  else
    let (head, args) := appHeadArgs body
    if isEtaArgSequence args arity && etaHeadClosedOverRemovedBinders head arity then
      head
    else
      e

partial def fixedPointReduce (fuel : Nat) (e : Expr) : MetaM Expr := do
  match fuel with
  | 0 => return e
  | fuel + 1 =>
      let reduced ← withTransparency .all <| reduce e false false true
      let etaReduced := etaReduceValue reduced
      if exprPayload [] etaReduced == exprPayload [] e then
        return etaReduced
      else
        fixedPointReduce fuel etaReduced

def runMetaWithEnv {α : Type} (env : Environment) (x : MetaM α) : IO (Except Exception α) := do
  let coreCtx : Core.Context := { fileName := "structural_dna", fileMap := default }
  let coreState : Core.State := { env := env }
  match ← (x.run {} {} |>.run coreCtx coreState).toIO' with
  | .ok ((value, _), _) => return .ok value
  | .error err => return .error err

def canonicalValue (env : Environment) (info : ConstantInfo) : IO (Option Expr) := do
  match info.value? (allowOpaque := true) with
  | none => return none
  | some value =>
      match ← runMetaWithEnv env (fixedPointReduce 16 value) with
      | .ok reduced => return some reduced
      | .error _ => return some (etaReduceValue value)

def reducedValueFingerprint (env : Environment) (params : List Name) (value : Expr) : IO String := do
  match ← runMetaWithEnv env (fixedPointReduce 16 value) with
  | .ok reduced => return exprFingerprint params reduced
  | .error _ => return exprFingerprint params (etaReduceValue value)

def isTheoremConstant (info : ConstantInfo) : Bool :=
  match info with
  | .thmInfo _ => true
  | _ => false

def valueIsProof (env : Environment) (value : Expr) : IO Bool := do
  match ← runMetaWithEnv env (Meta.isProof value) with
  | .ok isProof => return isProof
  | .error _ => return false

partial def stripLeadingLambdas (params : List Name) (e : Expr) : List LambdaBinder × Expr :=
  match e with
  | .lam _ ty body bi =>
      let (binders, inner) := stripLeadingLambdas params body
      ({
        binderInfo := binderInfoPayload bi,
        typePayload := exprPayload params ty
      } :: binders, inner)
  | .mdata _ inner => stripLeadingLambdas params inner
  | other => ([], other)

def classifierView (env : Environment) (info : ConstantInfo) : IO (Option ClassifierView) := do
  if isTheoremConstant info then
    return none
  else
    match info.value? (allowOpaque := true) with
    | none => return none
    | some value =>
        if ← valueIsProof env value then
          return none
        else
          match ← canonicalValue env info with
          | none => return none
          | some reduced =>
              let params := info.levelParams
              let (binders, body) := stripLeadingLambdas params reduced
              return some {
                name := info.name.toString,
                params := params,
                reducedExpr := reduced,
                lambdaBinders := binders,
                body := body,
                bodyFp := exprFingerprint params body,
                fullReducedFp := exprFingerprint params reduced
              }

def isAndExpr (e : Expr) : Option (Expr × Expr) :=
  let (head, args) := appHeadArgs e
  match head, args with
  | .const ``And _, [left, right] => some (left, right)
  | _, _ => none

def isTrivialLeaf : Expr → Bool
  | .mdata _ e => isTrivialLeaf e
  | .sort _ => true
  | .bvar _ => true
  | .const ``True _ => true
  | .const ``False _ => true
  | _ => false

partial def flattenAndWithPath (params : List Name) (path : String) (e : Expr) : List ConjunctLeaf :=
  match e with
  | .mdata _ inner => flattenAndWithPath params path inner
  | other =>
      match isAndExpr other with
      | some (left, right) =>
          flattenAndWithPath params (path ++ ".and.left") left ++
            flattenAndWithPath params (path ++ ".and.right") right
      | none =>
          [{
            path := path,
            expr := other,
            exprFp := exprFingerprint params other,
            isTrivial := isTrivialLeaf other
          }]

def flattenAnd (view : ClassifierView) : List ConjunctLeaf :=
  flattenAndWithPath view.params "body" view.body

def binderSignatureFp (binders : List LambdaBinder) : String :=
  stableHash (joinPayload "lambda-binders" (
    binders.map (fun b => joinPayload "binder" [b.binderInfo, b.typePayload])
  ))

def normalizerJson : Json :=
  Json.mkObj [
    ("beta", Json.bool true),
    ("eta", Json.bool true),
    ("zeta", Json.bool true),
    ("transparent_unfolding", Json.bool true),
    ("fuel", toJson (16 : Nat))
  ]

def relationEvidenceJson
    (candidate : ClassifierView)
    (prior : ClassifierView)
    (matched : ConjunctLeaf)
    (extraCount : Nat)
    (leaves : List ConjunctLeaf) : Json :=
  Json.mkObj [
    ("normal_form", Json.str "reduced_value"),
    ("binder_arity", toJson candidate.lambdaBinders.length),
    ("binder_signature_fp", Json.str (binderSignatureFp candidate.lambdaBinders)),
    ("prior_body_fp", Json.str prior.bodyFp),
    ("candidate_body_fp", Json.str candidate.bodyFp),
    ("matched_conjunct_path", Json.str matched.path),
    ("matched_path", Json.str matched.path),
    ("extra_conjunct_count", toJson extraCount),
    ("candidate_conjunct_fps", toJson (leaves.map (·.exprFp)))
  ]

def conjunctiveRefinementJson
    (candidateName priorName : String)
    (candidate prior : ClassifierView) : Option Json :=
  if candidate.lambdaBinders != prior.lambdaBinders then
    none
  else
    let leaves := flattenAnd candidate
    let matchedLeaves := (leaves.filter (fun leaf => leaf.exprFp == prior.bodyFp)).mergeSort
      (fun a b => a.path < b.path)
    match matchedLeaves with
    | [] => none
    | matched :: _ =>
        let extraCount := (leaves.filter (fun leaf => leaf.exprFp != prior.bodyFp && !leaf.isTrivial)).length
        if extraCount == 0 then
          none
        else
          some (Json.mkObj [
            ("relation", Json.str "conjunctive_refinement"),
            ("direction", Json.str "candidate_implies_prior"),
            ("grade_semantics", Json.str "semantic_projection"),
            ("prior", Json.str priorName),
            ("candidate", Json.str candidateName),
            ("evidence", relationEvidenceJson candidate prior matched extraCount leaves)
          ])

def declFingerprint (env : Environment) (info : ConstantInfo) : IO DeclFingerprint := do
  let params := info.levelParams
  let typeFp := exprFingerprint params info.type
  let constFp := exprFingerprint params (.const info.name (params.map Level.param))
  let valueFp ←
    if isTheoremConstant info then
      pure ""
    else
      match info.value? (allowOpaque := true) with
      | some value =>
          if ← valueIsProof env value then
            pure ""
          else
            pure (exprFingerprint params value)
      | none => pure ""
  let etaValueFp ←
    if isTheoremConstant info then
      pure ""
    else
      match info.value? (allowOpaque := true) with
      | some value =>
          if ← valueIsProof env value then
            pure ""
          else
            pure (exprFingerprint params (etaReduceValue value))
      | none => pure ""
  let reducedFingerprint ←
    if isTheoremConstant info then
      pure ""
    else
      match info.value? (allowOpaque := true) with
      | some value =>
          if ← valueIsProof env value then
            pure ""
          else
            reducedValueFingerprint env params value
      | none => pure ""
  let fingerprint :=
    stableHash (joinPayload "decl" [typeFp, valueFp])
  return {
    fingerprint := fingerprint,
    typeFp := typeFp,
    valueFp := valueFp,
    constFp := constFp,
    etaValueFp := etaValueFp,
    reducedFingerprint := reducedFingerprint
  }

def jsonForDeclFingerprint (fp : DeclFingerprint) : Json :=
  Json.mkObj [
    ("fingerprint", Json.str fp.fingerprint),
    ("type_fp", Json.str fp.typeFp),
    ("value_fp", Json.str fp.valueFp),
    ("const_fp", Json.str fp.constFp),
    ("eta_value_fp", Json.str fp.etaValueFp),
    ("reduced_fingerprint", Json.str fp.reducedFingerprint)
  ]

def parseJsonStringArray (j : Json) (field : String) : Except String (Array String) := do
  let arr ← (← j.getObjVal? field).getArr?
  arr.mapM (fun item => item.getStr?)

structure FingerprintRequest where
  imports : Array String
  decls : Array String

structure RelationRequest where
  imports : Array String
  candidates : Array String
  priors : Array String

inductive Request where
  | fingerprints : FingerprintRequest → Request
  | relations : RelationRequest → Request

def parseRelationRequest (j : Json) : Except String RelationRequest := do
  let imports ←
    match parseJsonStringArray j "imports" with
    | .ok imports => pure imports
    | .error _ => pure #["BEDC"]
  let relationObj ←
    match j.getObjVal? "relations" with
    | .ok relationObj => pure relationObj
    | .error _ => pure j
  let candidates ← parseJsonStringArray relationObj "candidates"
  let priors ← parseJsonStringArray relationObj "priors"
  return { imports := imports, candidates := candidates, priors := priors }

def readRequest (argv : List String) : IO Request := do
  if argv.length > 0 then
    let imports := ((argv.getD 0 "").splitOn ",").filter (· ≠ "")
    let decls := ((argv.getD 1 "").splitOn ",").filter (· ≠ "")
    return .fingerprints { imports := imports.toArray, decls := decls.toArray }
  else
    let stdin ← IO.getStdin
    let raw ← stdin.readToEnd
    match Json.parse raw with
    | .error err => throw (IO.userError s!"invalid JSON request: {err}")
    | .ok j =>
        if (j.getObjVal? "relations").isOk || (j.getObjVal? "candidates").isOk then
          match parseRelationRequest j with
          | .ok request => return .relations request
          | .error err => throw (IO.userError s!"invalid relations request: {err}")
        else
          match parseJsonStringArray j "imports", parseJsonStringArray j "decls" with
          | .ok imports, .ok decls =>
              return .fingerprints { imports := imports, decls := decls }
          | .error err, _ => throw (IO.userError s!"invalid imports field: {err}")
          | _, .error err => throw (IO.userError s!"invalid decls field: {err}")

def importSpec (moduleName : String) : Import :=
  { module := moduleName.toName, importAll := false, isExported := true, isMeta := false }

def initModuleSearchPath : IO Unit := do
  let sysroot ←
    match (← IO.getEnv "LEAN_SYSROOT") with
    | some path => pure (System.FilePath.mk path)
    | none => findSysroot
  let leanPath :=
    match (← IO.getEnv "LEAN_PATH") with
    | some path => System.SearchPath.parse path
    | none => []
  initSearchPath sysroot leanPath

unsafe def fingerprintsJson (imports decls : Array String) : IO Json := do
  withImportModules (imports.map importSpec) Options.empty fun env => do
    let mut out : List (String × Json) := []
    for decl in decls do
      let name := decl.toName
      match env.find? name with
      | some info =>
          out := (decl, jsonForDeclFingerprint (← declFingerprint env info)) :: out
      | none =>
          throw (IO.userError s!"declaration not found: {decl}")
    return Json.mkObj out.reverse

unsafe def relationsJson (request : RelationRequest) : IO Json := do
  withImportModules (request.imports.map importSpec) Options.empty fun env => do
    let mut views : List (String × ClassifierView) := []
    let names := (request.candidates.toList ++ request.priors.toList).eraseDups
    for decl in names do
      match env.find? decl.toName with
      | some info =>
          match ← classifierView env info with
          | some view => views := (decl, view) :: views
          | none => pure ()
      | none => throw (IO.userError s!"declaration not found: {decl}")
    let findView? (name : String) : Option ClassifierView :=
      match views.find? (fun item => item.fst == name) with
      | some item => some item.snd
      | none => none
    let mut relations : List Json := []
    for candidateName in request.candidates do
      for priorName in request.priors do
        if candidateName != priorName then
          match findView? candidateName, findView? priorName with
          | some candidate, some prior =>
              match conjunctiveRefinementJson candidateName priorName candidate prior with
              | some relation => relations := relation :: relations
              | none => pure ()
          | _, _ => pure ()
    return Json.mkObj [
      ("schema", Json.str "bedc.structural_dna.relations"),
      ("normalizer", normalizerJson),
      ("relations", Json.arr (relations.reverse.toArray))
    ]

def testImports : Array String :=
  #["scripts.structural_dna.TestTargets"]

def testDecls : Array String :=
  #[
    "BEDC.StructuralDna.TestTargets.TA",
    "BEDC.StructuralDna.TestTargets.TB",
    "BEDC.StructuralDna.TestTargets.FA",
    "BEDC.StructuralDna.TestTargets.FB",
    "BEDC.StructuralDna.TestTargets.C1",
    "BEDC.StructuralDna.TestTargets.C2",
    "BEDC.StructuralDna.TestTargets.C1DirectEta",
    "BEDC.StructuralDna.TestTargets.C1LetEta",
    "BEDC.StructuralDna.TestTargets.C1MidEta",
    "BEDC.StructuralDna.TestTargets.C1MultiEta",
    "BEDC.StructuralDna.TestTargets.BaseClassifier",
    "BEDC.StructuralDna.TestTargets.ExtendedClassifier",
    "BEDC.StructuralDna.TestTargets.ReorderedClassifier",
    "BEDC.StructuralDna.TestTargets.SharedOnlyClassifier",
    "BEDC.StructuralDna.TestTargets.FixedShapeClassifier",
    "BEDC.StructuralDna.TestTargets.ExtendedEtaClassifier",
    "BEDC.StructuralDna.TestTargets.HeadDependsClassifier",
    "BEDC.StructuralDna.TestTargets.Hollow",
    "BEDC.StructuralDna.TestTargets.SomeP",
    "BEDC.StructuralDna.TestTargets.ExplicitArrow",
    "BEDC.StructuralDna.TestTargets.ImplicitArrow",
    "BEDC.StructuralDna.TestTargets.InstanceArrow",
    "BEDC.StructuralDna.TestTargets.AlphaLamA",
    "BEDC.StructuralDna.TestTargets.AlphaLamB",
    "BEDC.StructuralDna.TestTargets.PropDefTrue",
    "BEDC.StructuralDna.TestTargets.PropDefFalse",
    "BEDC.StructuralDna.TestTargets.PropDefEq",
    "BEDC.StructuralDna.TestTargets.ProofA",
    "BEDC.StructuralDna.TestTargets.ProofB"
  ]

def getFp! (items : List (String × DeclFingerprint)) (name : String) : IO String := do
  match items.find? (fun item => item.fst == name) with
  | some item => return item.snd.fingerprint
  | none => throw (IO.userError s!"test declaration missing: {name}")

def getReducedFp! (items : List (String × DeclFingerprint)) (name : String) : IO String := do
  match items.find? (fun item => item.fst == name) with
  | some item => return item.snd.reducedFingerprint
  | none => throw (IO.userError s!"test declaration missing: {name}")

def printCheck (label : String) (ok : Bool) : IO Bool := do
  IO.println s!"{label}: {if ok then "PASS" else "FAIL"}"
  return ok

def hasRelation (relations : List Json) (candidate prior relationName : String) : Bool :=
  relations.any (fun item =>
    match item.getObjVal? "candidate", item.getObjVal? "prior", item.getObjVal? "relation" with
    | .ok c, .ok p, .ok r =>
        c.getStr?.toOption == some candidate
          && p.getStr?.toOption == some prior
          && r.getStr?.toOption == some relationName
    | _, _, _ => false)

unsafe def relationSelfTest : IO Bool := do
  let req : RelationRequest := {
    imports := testImports
    candidates := #[
      "BEDC.StructuralDna.TestTargets.ExtendedClassifier",
      "BEDC.StructuralDna.TestTargets.ReorderedClassifier",
      "BEDC.StructuralDna.TestTargets.SharedOnlyClassifier",
      "BEDC.StructuralDna.TestTargets.FixedShapeClassifier",
      "BEDC.StructuralDna.TestTargets.ExtendedEtaClassifier"
    ]
    priors := #[
      "BEDC.StructuralDna.TestTargets.BaseClassifier",
      "BEDC.StructuralDna.TestTargets.ExtendedClassifier"
    ]
  }
  let raw ← relationsJson req
  let relations :=
    match raw.getObjVal? "relations" with
    | .ok rels =>
        match rels.getArr? with
        | .ok arr => arr.toList
        | .error _ => []
    | .error _ => []
  let base := "BEDC.StructuralDna.TestTargets.BaseClassifier"
  let extended := "BEDC.StructuralDna.TestTargets.ExtendedClassifier"
  let reordered := "BEDC.StructuralDna.TestTargets.ReorderedClassifier"
  let sharedOnly := "BEDC.StructuralDna.TestTargets.SharedOnlyClassifier"
  let fixedShape := "BEDC.StructuralDna.TestTargets.FixedShapeClassifier"
  let extendedEta := "BEDC.StructuralDna.TestTargets.ExtendedEtaClassifier"
  let r1 ← printCheck "R1 conjunctive refinement extension" (
    hasRelation relations extended base "conjunctive_refinement"
  )
  let r2 ← printCheck "R2 conjunctive refinement reordered" (
    hasRelation relations reordered base "conjunctive_refinement"
  )
  let r3 ← printCheck "R3 disjunction not refinement" (
    !hasRelation relations sharedOnly base "conjunctive_refinement"
  )
  let r4 ← printCheck "R4 fixed shape not refinement" (
    !hasRelation relations fixedShape base "conjunctive_refinement"
  )
  let r5 ← printCheck "R5 eta wrapper not positive relation" (
    !hasRelation relations extendedEta extended "conjunctive_refinement"
  )
  return [r1, r2, r3, r4, r5].all id

unsafe def runSelfTest : IO UInt32 := do
  let items ← withImportModules (testImports.map importSpec) Options.empty fun env => do
    let mut out : List (String × DeclFingerprint) := []
    for decl in testDecls do
      match env.find? decl.toName with
      | some info => out := (decl, ← declFingerprint env info) :: out
      | none => throw (IO.userError s!"test declaration not found: {decl}")
    return out
  let ta ← getFp! items "BEDC.StructuralDna.TestTargets.TA"
  let tb ← getFp! items "BEDC.StructuralDna.TestTargets.TB"
  let fa ← getFp! items "BEDC.StructuralDna.TestTargets.FA"
  let fb ← getFp! items "BEDC.StructuralDna.TestTargets.FB"
  let c1 ← getFp! items "BEDC.StructuralDna.TestTargets.C1"
  let c2 ← getFp! items "BEDC.StructuralDna.TestTargets.C2"
  let c1Reduced ← getReducedFp! items "BEDC.StructuralDna.TestTargets.C1"
  let c2Reduced ← getReducedFp! items "BEDC.StructuralDna.TestTargets.C2"
  let c1DirectEtaReduced ← getReducedFp! items "BEDC.StructuralDna.TestTargets.C1DirectEta"
  let c1LetEtaReduced ← getReducedFp! items "BEDC.StructuralDna.TestTargets.C1LetEta"
  let c1MidEtaReduced ← getReducedFp! items "BEDC.StructuralDna.TestTargets.C1MidEta"
  let c1MultiEtaReduced ← getReducedFp! items "BEDC.StructuralDna.TestTargets.C1MultiEta"
  let headDependsReduced ←
    getReducedFp! items "BEDC.StructuralDna.TestTargets.HeadDependsClassifier"
  let hollow ← getFp! items "BEDC.StructuralDna.TestTargets.Hollow"
  let someP ← getFp! items "BEDC.StructuralDna.TestTargets.SomeP"
  let explicitArrow ← getFp! items "BEDC.StructuralDna.TestTargets.ExplicitArrow"
  let implicitArrow ← getFp! items "BEDC.StructuralDna.TestTargets.ImplicitArrow"
  let instanceArrow ← getFp! items "BEDC.StructuralDna.TestTargets.InstanceArrow"
  let alphaLamA ← getFp! items "BEDC.StructuralDna.TestTargets.AlphaLamA"
  let alphaLamB ← getFp! items "BEDC.StructuralDna.TestTargets.AlphaLamB"
  let propDefTrue ← getFp! items "BEDC.StructuralDna.TestTargets.PropDefTrue"
  let propDefFalse ← getFp! items "BEDC.StructuralDna.TestTargets.PropDefFalse"
  let propDefEq ← getFp! items "BEDC.StructuralDna.TestTargets.PropDefEq"
  let proofA ← getFp! items "BEDC.StructuralDna.TestTargets.ProofA"
  let proofB ← getFp! items "BEDC.StructuralDna.TestTargets.ProofB"
  let t1 ← printCheck "T1 lam alpha" (ta == tb)
  let t2 ← printCheck "T2 forall alpha" (fa == fb)
  let t3 ← printCheck "T3 classifier distinction" (c1 != c2)
  let t4 ← printCheck "T4 hollow distinction" (hollow != someP)
  let t5 ← printCheck "T5 binderInfo distinction" (
    explicitArrow != implicitArrow
    && explicitArrow != instanceArrow
    && implicitArrow != instanceArrow
  )
  let t6 ← printCheck "T6 binder-name alpha" (alphaLamA == alphaLamB)
  let t7 ← printCheck "T7 theorem proof irrelevance" (proofA == proofB)
  let t8 ← printCheck "T8 Prop-valued def distinction" (
    propDefTrue != propDefFalse
    && propDefTrue != propDefEq
    && propDefFalse != propDefEq
  )
  let t10 ← printCheck "T10 reduced eta equivalence" (
    c1Reduced == c1DirectEtaReduced
    && c1Reduced == c1LetEtaReduced
    && c1Reduced == c1MidEtaReduced
    && c1Reduced == c1MultiEtaReduced
    && c1Reduced != c2Reduced
  )
  let t11 ← printCheck "T11 eta head dependency preserved" (
    headDependsReduced != someP
    && headDependsReduced != c1Reduced
    && headDependsReduced != c2Reduced
  )
  let relationTests ← relationSelfTest
  return if [t1, t2, t3, t4, t5, t6, t7, t8, t10, t11, relationTests].all id then 0 else 1

end BEDC.StructuralDna

unsafe def main (argv : List String) : IO UInt32 := do
  BEDC.StructuralDna.initModuleSearchPath
  match argv with
  | ["--self-test"] => BEDC.StructuralDna.runSelfTest
  | _ =>
      let request ← BEDC.StructuralDna.readRequest argv
      let json ←
        match request with
        | .fingerprints req => BEDC.StructuralDna.fingerprintsJson req.imports req.decls
        | .relations req => BEDC.StructuralDna.relationsJson req
      IO.println json.compress
      return 0
