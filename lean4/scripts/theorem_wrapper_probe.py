#!/usr/bin/env python3
"""Informational one-step theorem-wrapper probe for BEDC Lean theorems.

The probe imports requested modules in Lean, reads theorem proof terms through
`getConstInfo`, and reports high-confidence theorem wrappers whose proof body is
just an older theorem/definition applied to forwarded binders and closed
specialization arguments. It is a cheap theorem-count inflation proxy, not a gate
unless `--strict` is passed.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path


DEFAULT_LEAN_ROOT = str(Path(__file__).resolve().parents[1])
LEAN_ROOT = os.environ.get("BEDC_LEAN_ROOT", DEFAULT_LEAN_ROOT)

MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
NAME_RE = MODULE_RE
RESULT_PREFIX = "THEOREM_WRAPPER_PROBE_JSON:"

DEFAULT_TARGETS = [
    "BEDC.Derived.Sqrt2RatBridge:sqrt2RatBridge_pow_two_cofinal_nat",
    "BEDC.Derived.LahNumberUp:lahNumber_zero_zero",
    "BEDC.Derived.WilsonQuotientUp:wilsonQuotientNat_thirteen_mod_zero",
]


@dataclass(frozen=True)
class Target:
    module: str
    name: str


LEAN_META = r"""
import Lean
open Lean Meta

set_option linter.unusedVariables false

def resultPrefix : String := "THEOREM_WRAPPER_PROBE_JSON:"

structure ProbeTarget where
  moduleName : String
  rawName : String

structure Spine where
  head : Expr
  args : Array Expr
  peeled : Array String
deriving Nonempty

def jsonStrArray (items : Array String) : Json :=
  Json.arr (items.map Json.str)

def jsonBool (value : Bool) : Json :=
  Json.bool value

def stringEndsWith (s suffix : String) : Bool :=
  s.endsWith suffix

def stringContainsAny (s : String) (needles : Array String) : Bool :=
  needles.any (fun needle => s.contains needle)

def nameLeaf (name : Name) : String :=
  name.getString!

def isWrapperIntentName (name : Name) : Bool :=
  stringContainsAny name.toString #[
    "_bridge", "_export", "_surface", "_nat_surface", "_unfold", "_value",
    "_length", "_unary", "_from_", "_of_", "_stack", "_constructive_export",
    "_small_export"
  ]

def isMatcherName (name : Name) : Bool :=
  let s := name.toString
  s.contains ".match_" || s.contains "._match_" || s.contains ".matcher" ||
    stringEndsWith s ".below" || stringEndsWith s ".brecOn"

def isRecursorLikeName (name : Name) : Bool :=
  let leaf := nameLeaf name
  leaf == "rec" || leaf == "recOn" || leaf == "recAux" ||
    leaf == "brecOn" || leaf == "casesOn"

def isStructuralConstName (name : Name) : Bool :=
  let leaf := nameLeaf name
  name == ``Eq.refl || name == ``True.intro || name == ``And.intro ||
    name == ``Exists.intro || leaf == "rfl" || isMatcherName name ||
    isRecursorLikeName name

def isEqReflHead (head : Expr) : Bool :=
  match head.consumeMData with
  | Expr.const name _ => name == ``Eq.refl
  | _ => false

partial def collectAppArgs : Expr -> Array Expr
  | Expr.app fn arg => (collectAppArgs fn).push arg
  | Expr.mdata _ body => collectAppArgs body
  | _ => #[]

partial def collectAppHead : Expr -> Expr
  | Expr.app fn _ => collectAppHead fn
  | Expr.mdata _ body => collectAppHead body
  | e => e

def collectApp (e : Expr) : Expr × Array Expr :=
  (collectAppHead e.consumeMData, collectAppArgs e.consumeMData)

def isTruePropExpr (e : Expr) : Bool :=
  e.consumeMData.isConstOf ``True

def isBareReflEqPropExpr (e : Expr) : Bool :=
  match e.consumeMData with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) lhs) rhs => lhs == rhs
  | _ => false

def conclusionIsTrue (targetType : Expr) : Bool :=
  isTruePropExpr targetType.consumeMData

def hasAnyTargetFVar (e : Expr) (targetFVars : Array FVarId) : Bool :=
  targetFVars.any (fun fvarId => e.containsFVar fvarId)

def isForwardedFVar (e : Expr) (targetFVars : Array FVarId) : Bool :=
  match e.consumeMData with
  | Expr.fvar fvarId => targetFVars.any (fun id => id == fvarId)
  | _ => false

def headConst? (e : Expr) : Option Name :=
  match e.consumeMData with
  | Expr.const name _ => some name
  | _ => none

def resultName (moduleName rawName : String) (declName : Name) : Json :=
  Json.mkObj [
    ("module", Json.str moduleName),
    ("requested_name", Json.str rawName),
    ("name", Json.str declName.toString)
  ]

def findTargetName (moduleName rawName : String) : CoreM (Except String Name) := do
  let env <- getEnv
  let direct := rawName.toName
  if env.contains direct then
    return Except.ok direct
  let qualified := (moduleName ++ "." ++ rawName).toName
  if env.contains qualified then
    return Except.ok qualified
  return Except.error s!"unknown theorem {rawName} in module {moduleName}"

def isTheoremOrDefInfo : ConstantInfo -> Bool
  | ConstantInfo.thmInfo _ => true
  | ConstantInfo.defnInfo _ => true
  | ConstantInfo.opaqueInfo _ => true
  | _ => false

def isTheoremInfo : ConstantInfo -> Bool
  | ConstantInfo.thmInfo _ => true
  | _ => false

def headModuleString (name : Name) : CoreM String := do
  let env <- getEnv
  match env.getModuleIdxFor? name with
  | some idx => return (env.header.moduleNames[idx]!).toString
  | none => return ""

def constantUsableAsWrapperHead (declName oldName : Name) : CoreM Bool := do
  let env <- getEnv
  if oldName == declName then
    return false
  if isStructuralConstName oldName then
    return false
  if env.isConstructor oldName || env.isProjectionFn oldName then
    return false
  if isMatcherName oldName then
    return false
  match env.find? oldName with
  | some info =>
      match info with
      | ConstantInfo.recInfo _ => return false
      | ConstantInfo.ctorInfo _ => return false
      | _ => return isTheoremOrDefInfo info
  | none => return false

partial def containsBadStructuralNode (env : Environment) (e : Expr) : Bool :=
  match e.consumeMData with
  | Expr.const name _ =>
      isMatcherName name || isRecursorLikeName name ||
        (match env.find? name with
        | some (ConstantInfo.recInfo _) => true
        | _ => false)
  | Expr.app fn arg => containsBadStructuralNode env fn || containsBadStructuralNode env arg
  | Expr.lam _ type body _ =>
      containsBadStructuralNode env type || containsBadStructuralNode env body
  | Expr.forallE _ type body _ =>
      containsBadStructuralNode env type || containsBadStructuralNode env body
  | Expr.letE _ type value body _ =>
      containsBadStructuralNode env type || containsBadStructuralNode env value ||
        containsBadStructuralNode env body
  | Expr.mdata _ body => containsBadStructuralNode env body
  | Expr.proj _ _ body => containsBadStructuralNode env body
  | _ => false

partial def containsComplexSyntax (e : Expr) : Bool :=
  match e.consumeMData with
  | Expr.lam .. => true
  | Expr.letE .. => true
  | Expr.forallE .. => true
  | Expr.app fn arg => containsComplexSyntax fn || containsComplexSyntax arg
  | Expr.mdata _ body => containsComplexSyntax body
  | Expr.proj _ _ body => containsComplexSyntax body
  | _ => false

def isReflLikeArg (e : Expr) : Bool :=
  let (head, _args) := collectApp e.consumeMData
  match headConst? head with
  | some name => name == ``Eq.refl || nameLeaf name == "rfl"
  | none => false

def isOldProofConstantArg (env : Environment) (e : Expr) (declName : Name)
    (targetFVars : Array FVarId) : Bool :=
  let (head, args) := collectApp e.consumeMData
  match headConst? head with
  | some name =>
      name != declName &&
      !isStructuralConstName name &&
      !hasAnyTargetFVar e targetFVars &&
      !containsBadStructuralNode env e &&
      args.all (fun arg => !containsComplexSyntax arg) &&
      (match env.find? name with
      | some info => isTheoremInfo info
      | none => false)
  | none => false

def classifyArg (env : Environment) (declName : Name) (targetFVars : Array FVarId)
    (arg : Expr) : String :=
  if isForwardedFVar arg targetFVars then
    "forwarded_fvar"
  else if isReflLikeArg arg then
    "refl_like"
  else if isOldProofConstantArg env arg declName targetFVars then
    "old_proof_constant"
  else if !hasAnyTargetFVar arg targetFVars && !containsComplexSyntax arg &&
      !containsBadStructuralNode env arg then
    "closed_value"
  else
    "complex_arg"

def allAllowedArgClasses (classes : Array String) : Bool :=
  classes.all (fun cls =>
    cls == "forwarded_fvar" || cls == "closed_value" ||
      cls == "refl_like" || cls == "old_proof_constant")

def hasSpecializationOrRenameSignal (classes : Array String) (headModule moduleName : String)
    (headName declName : Name) : Bool :=
  classes.any (fun cls => cls == "closed_value" || cls == "old_proof_constant" ||
    cls == "refl_like") ||
  headModule != "" && headModule != moduleName ||
  nameLeaf headName != nameLeaf declName

partial def peelThinShells (e : Expr) (peeled : Array String) : Spine :=
  let (head, args) := collectApp e.consumeMData
  match headConst? head with
  | some name =>
      if (name == ``Eq.ndrec || name == ``Eq.rec || name == ``Eq.recOn ||
          name == ``cast) && args.size > 0 then
        peelThinShells args[args.size - 1]! (peeled.push name.toString)
      else
        { head := head, args := args, peeled := peeled }
  | none => { head := head, args := args, peeled := peeled }

def probeTheorem (target : ProbeTarget) : CoreM Json := do
  match (<- findTargetName target.moduleName target.rawName) with
  | Except.error err =>
      return Json.mkObj [
        ("module", Json.str target.moduleName),
        ("requested_name", Json.str target.rawName),
        ("error", Json.str err),
        ("head_constant", Json.str ""),
        ("head_module", Json.str ""),
        ("confidence", Json.str "none"),
        ("arg_classes", Json.arr #[]),
        ("wrapper_intent_name", Json.bool false),
        ("reason", Json.str "target lookup failed"),
        ("candidate", Json.bool false)
      ]
  | Except.ok declName =>
      let ci <- getConstInfo declName
      match ci with
      | ConstantInfo.thmInfo tv =>
          MetaM.run' do
            forallTelescope tv.type fun typeVars targetType => do
              lambdaTelescope tv.value fun valueVars body => do
                let body <- instantiateMVars body
                let env <- getEnv
                let targetFVars := valueVars.map Expr.fvarId!
                let targetType <- instantiateMVars targetType
                let wrapperIntent := isWrapperIntentName declName
                let spine := peelThinShells body.consumeMData #[]
                let headName? := headConst? spine.head
                let bodyHasBadStructural := containsBadStructuralNode env body
                let conclusionTrue := conclusionIsTrue targetType
                match headName? with
                | none =>
                    pure <| Json.mkObj [
                      ("module", Json.str target.moduleName),
                      ("requested_name", Json.str target.rawName),
                      ("name", Json.str declName.toString),
                      ("head_constant", Json.str ""),
                      ("head_module", Json.str ""),
                      ("confidence", Json.str "none"),
                      ("arg_classes", Json.arr #[]),
                      ("wrapper_intent_name", Json.bool wrapperIntent),
                      ("reason", Json.str "proof head is not a constant"),
                      ("candidate", Json.bool false)
                    ]
                | some headName =>
                    let headModule <- headModuleString headName
                    let argClasses := spine.args.map (classifyArg env declName targetFVars)
                    let headOk <- constantUsableAsWrapperHead declName headName
                    let allowedArgs := allAllowedArgClasses argClasses
                    let signal := hasSpecializationOrRenameSignal
                      argClasses headModule target.moduleName headName declName
                    let candidate :=
                      headOk && allowedArgs && !bodyHasBadStructural &&
                      !conclusionTrue && !wrapperIntent && signal
                    let reason :=
                      if candidate then
                        "single theorem/definition head applied only to forwarded binders, closed values, refl-like proofs, or old proof constants"
                      else if wrapperIntent then
                        "name carries wrapper-intent marker"
                      else if conclusionTrue then
                        "conclusion is True"
                      else if !headOk then
                        "proof head is not an eligible older theorem/definition constant"
                      else if bodyHasBadStructural then
                        "proof body contains recursor or matcher"
                      else if !allowedArgs then
                        "proof head has complex target-local or structural arguments"
                      else if !signal then
                        "no closed specialization, old-proof argument, cross-module head, or rename signal"
                      else
                        "not a high-confidence wrapper"
                    let confidence :=
                      if candidate then "high"
                      else if wrapperIntent && headOk && allowedArgs && !bodyHasBadStructural &&
                          !conclusionTrue then "wrapper_intent"
                      else "none"
                    pure <| Json.mkObj [
                      ("module", Json.str target.moduleName),
                      ("requested_name", Json.str target.rawName),
                      ("name", Json.str declName.toString),
                      ("head_constant", Json.str headName.toString),
                      ("head_module", Json.str headModule),
                      ("confidence", Json.str confidence),
                      ("arg_classes", jsonStrArray argClasses),
                      ("wrapper_intent_name", Json.bool wrapperIntent),
                      ("reason", Json.str reason),
                      ("candidate", Json.bool candidate),
                      ("peeled_thin_shells", jsonStrArray spine.peeled)
                    ]
      | _ =>
          return Json.mkObj [
            ("module", Json.str target.moduleName),
            ("requested_name", Json.str target.rawName),
            ("name", Json.str declName.toString),
            ("error", Json.str "constant is not a theorem"),
            ("head_constant", Json.str ""),
            ("head_module", Json.str ""),
            ("confidence", Json.str "none"),
            ("arg_classes", Json.arr #[]),
            ("wrapper_intent_name", Json.bool (isWrapperIntentName declName)),
            ("reason", Json.str "constant is not a theorem"),
            ("candidate", Json.bool false)
          ]

def runProbe (targets : Array ProbeTarget) : CoreM Unit := do
  let mut rows : Array Json := #[]
  for target in targets do
    rows := rows.push (<- probeTheorem target)
  IO.println (resultPrefix ++ Json.compress (Json.arr rows))
"""


def lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=True)


def validate_module(module: str) -> None:
    if not MODULE_RE.match(module):
        raise ValueError(f"invalid Lean module name: {module}")


def validate_name(name: str) -> None:
    if not NAME_RE.match(name):
        raise ValueError(f"invalid Lean declaration name: {name}")


def parse_targets(raw: str | None) -> list[Target]:
    if raw is None or not raw.strip():
        raw_items = DEFAULT_TARGETS
    else:
        raw_items = [item.strip() for item in raw.split(",") if item.strip()]
    targets: list[Target] = []
    for item in raw_items:
        if ":" not in item:
            raise ValueError(f"target must be module:name, got: {item}")
        module, name = item.split(":", 1)
        module = module.strip()
        name = name.strip()
        validate_module(module)
        validate_name(name)
        targets.append(Target(module=module, name=name))
    if not targets:
        raise ValueError("no targets supplied")
    return targets


def lean_target_array(targets: list[Target]) -> str:
    rows = []
    for target in targets:
        rows.append(
            "{ moduleName := "
            + lean_string(target.module)
            + ", rawName := "
            + lean_string(target.name)
            + " }"
        )
    return "#[" + ", ".join(rows) + "]"


def build_lean_source(targets: list[Target], canary: bool = False) -> str:
    modules = sorted({target.module for target in targets if target.module != "_canary"})
    imports = ["import " + module for module in modules]
    canary_block = ""
    if canary:
        canary_block = """
def canary_id (n : Nat) : Nat := n

theorem canary_base_alias (n : Nat) : n = n := by
  rfl

theorem canary_alias (n : Nat) : n = n :=
  canary_base_alias n

theorem canary_base_special (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n

theorem canary_special_zero : 0 + 0 = 0 :=
  canary_base_special 0

theorem canary_rfl (n : Nat) : canary_id n = n := by
  rfl

theorem canary_induction (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Nat.succ (0 + n) = Nat.succ n
      exact congrArg Nat.succ ih
"""
    return (
        "\n".join(imports)
        + "\n"
        + LEAN_META
        + canary_block
        + "\n#eval show CoreM Unit from runProbe "
        + lean_target_array(targets)
        + "\n"
    )


def run_lean(targets: list[Target], canary: bool = False) -> tuple[list[dict], str]:
    if not os.path.isdir(LEAN_ROOT):
        raise RuntimeError(f"Lean root does not exist: {LEAN_ROOT}")
    source = build_lean_source(targets, canary=canary)
    proc = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        input=source,
        text=True,
        cwd=LEAN_ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    stdout_log = "\n".join(
        line for line in proc.stdout.splitlines() if not line.startswith(RESULT_PREFIX)
    ).strip()
    combined_log = "\n".join(part for part in (stdout_log, proc.stderr.strip()) if part)
    result_line = None
    for line in proc.stdout.splitlines():
        if line.startswith(RESULT_PREFIX):
            result_line = line[len(RESULT_PREFIX):]
    if proc.returncode != 0:
        raise RuntimeError(
            "Lean probe failed with exit code "
            + str(proc.returncode)
            + ("\n" + combined_log if combined_log else "")
        )
    if result_line is None:
        raise RuntimeError("Lean probe did not emit JSON result\n" + combined_log)
    try:
        parsed = json.loads(result_line)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"Lean probe emitted invalid JSON: {exc}") from exc
    if not isinstance(parsed, list):
        raise RuntimeError("Lean probe JSON was not an array")
    return parsed, combined_log


def candidates_from_results(results: list[dict]) -> list[dict]:
    candidates: list[dict] = []
    for row in results:
        if row.get("candidate") is True:
            candidates.append(
                {
                    "name": row.get("name", row.get("requested_name", "")),
                    "module": row.get("module", ""),
                    "head_constant": row.get("head_constant", ""),
                    "head_module": row.get("head_module", ""),
                    "confidence": row.get("confidence", ""),
                    "arg_classes": row.get("arg_classes", []),
                }
            )
    return candidates


def make_output(results: list[dict], note: str, extra: dict | None = None) -> dict:
    out = {
        "scanned": len(results),
        "candidates": candidates_from_results(results),
        "results": results,
        "_note": note,
    }
    if extra:
        out.update(extra)
    return out


def run_self_test() -> int:
    targets = [
        Target("_canary", "canary_alias"),
        Target("_canary", "canary_special_zero"),
        Target("_canary", "canary_rfl"),
        Target("_canary", "canary_induction"),
    ]
    results, _log = run_lean(targets, canary=True)
    by_requested = {row.get("requested_name"): row for row in results}
    alias = by_requested.get("canary_alias", {})
    special = by_requested.get("canary_special_zero", {})
    rfl = by_requested.get("canary_rfl", {})
    induction = by_requested.get("canary_induction", {})
    checks = {
        "TP1_alias": (
            alias.get("candidate") is True
            and alias.get("head_constant") == "canary_base_alias"
            and alias.get("arg_classes") == ["forwarded_fvar"]
        ),
        "TP2_closed_special": (
            special.get("candidate") is True
            and special.get("head_constant") == "canary_base_special"
            and special.get("arg_classes") == ["closed_value"]
        ),
        "TN1_rfl": rfl.get("candidate") is False,
        "TN2_induction": induction.get("candidate") is False,
    }
    passed = all(checks.values())
    out = make_output(
        results,
        "self-test canaries check direct alias, closed specialization, definitional rfl, and induction/recursor rejection.",
        {
            "self_test": "PASS" if passed else "FAIL",
            "checks": checks,
        },
    )
    print(json.dumps(out, ensure_ascii=False, indent=2))
    return 0 if passed else 1


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Informational Lean proof-term one-step theorem-wrapper probe."
    )
    parser.add_argument(
        "--targets",
        help="comma-separated module:name targets; default uses a small pilot list",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="exit 1 when any high-confidence one-step theorem wrapper is found",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run four canary theorems and fail unless all detector expectations pass",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        if args.self_test:
            return run_self_test()
        targets = parse_targets(args.targets)
        grouped: dict[str, list[Target]] = defaultdict(list)
        for target in targets:
            grouped[target.module].append(target)
        all_results: list[dict] = []
        logs: list[str] = []
        for module_targets in grouped.values():
            results, log = run_lean(module_targets)
            all_results.extend(results)
            if log:
                logs.append(log)
        out = make_output(
            all_results,
            "informational only: candidates are high-confidence one-step theorem wrappers in static proof-term spine analysis; --strict turns candidates into exit 1.",
        )
        if logs:
            out["lean_log"] = "\n".join(logs)
        print(json.dumps(out, ensure_ascii=False, indent=2))
        if args.strict and out["candidates"]:
            return 1
        return 0
    except Exception as exc:
        out = {
            "scanned": 0,
            "candidates": [],
            "results": [],
            "error": str(exc),
            "_note": "theorem_wrapper_probe failed before producing a sound audit result.",
        }
        print(json.dumps(out, ensure_ascii=False, indent=2))
        return 2


if __name__ == "__main__":
    sys.exit(main())
