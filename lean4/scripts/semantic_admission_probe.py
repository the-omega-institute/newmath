#!/usr/bin/env python3
"""Informational premise-insensitivity probe for BEDC Lean theorems.

The probe imports requested modules in Lean, reads theorem proof terms through
`getConstInfo`, and reports explicit propositional premises whose proof binder
does not occur in the proof body. It is a cheap SPAG proxy, not a gate unless
`--strict` is passed.
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


DEFAULT_LEAN_ROOT = "/Users/chronoai/newmath/lean4"
LEAN_ROOT = os.environ.get("BEDC_LEAN_ROOT", DEFAULT_LEAN_ROOT)

MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
NAME_RE = MODULE_RE
RESULT_PREFIX = "SEMANTIC_ADMISSION_PROBE_JSON:"

DEFAULT_TARGETS = [
    "BEDC.Derived.StirlingFirstUp:stirlingFirst_self_and_above",
    "BEDC.Derived.StirlingFirstUp:stirlingFirst_succ_prefix_recurrence",
    "BEDC.Derived.Window6Zeckendorf:zfib_weaken_le",
    "BEDC.Derived.RationalUp.RatLaws:BEDC.Derived.RationalUp.intOfNat_hsame_congr",
]


@dataclass(frozen=True)
class Target:
    module: str
    name: str


LEAN_META = r"""
import Lean
open Lean Meta

set_option linter.unusedVariables false

def resultPrefix : String := "SEMANTIC_ADMISSION_PROBE_JSON:"

structure ProbeTarget where
  moduleName : String
  rawName : String

def jsonStrArray (items : Array String) : Json :=
  Json.arr (items.map Json.str)

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

def isTruePropExpr (e : Expr) : Bool :=
  e.consumeMData.isConstOf ``True

def isReflEqPropExpr (e : Expr) : Bool :=
  match e.consumeMData with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) lhs) rhs => lhs == rhs
  | _ => false

partial def headConstName? : Expr -> Option Name
  | Expr.const name _ => some name
  | Expr.app fn _ => headConstName? fn
  | Expr.mdata _ body => headConstName? body
  | _ => none

def isBareAnchorName (name : Name) : Bool :=
  let leaf := name.getString!
  leaf == "Anchor" || leaf == "Anchored" || leaf.endsWith "Anchor" ||
    leaf.endsWith "AnchorProp"

def isBareAnchorPropExpr (e : Expr) : Bool :=
  match headConstName? e.consumeMData with
  | some name => isBareAnchorName name
  | none => false

def eligiblePremise (typeFVar : Expr) : MetaM Bool := do
  let decl <- typeFVar.fvarId!.getDecl
  if !decl.binderInfo.isExplicit then
    return false
  let typeExpr <- instantiateMVars (<- inferType typeFVar)
  let prop <- isProp typeExpr
  if !prop then
    return false
  if (<- isClass? typeExpr).isSome then
    return false
  let typeWhnf <- whnf typeExpr
  return !(isTruePropExpr typeWhnf) &&
    !(isReflEqPropExpr typeWhnf) &&
    !(isBareAnchorPropExpr typeWhnf)

def probeTheorem (target : ProbeTarget) : CoreM Json := do
  match (<- findTargetName target.moduleName target.rawName) with
  | Except.error err =>
      return Json.mkObj [
        ("module", Json.str target.moduleName),
        ("requested_name", Json.str target.rawName),
        ("error", Json.str err),
        ("premises", Json.arr #[])
      ]
  | Except.ok declName =>
      let ci <- getConstInfo declName
      match ci with
      | ConstantInfo.thmInfo tv =>
          MetaM.run' do
            forallTelescope tv.type fun typeVars _ => do
              lambdaTelescope tv.value fun valueVars body => do
                let body <- instantiateMVars body
                let count := Nat.min typeVars.size valueVars.size
                let mut premises : Array Json := #[]
                for i in [:count] do
                  if (<- eligiblePremise typeVars[i]!) then
                    let typeDecl <- typeVars[i]!.fvarId!.getDecl
                    let typeExpr <- instantiateMVars (<- inferType typeVars[i]!)
                    let typePretty <- ppExpr typeExpr
                    let used := body.containsFVar valueVars[i]!.fvarId!
                    premises := premises.push <| Json.mkObj [
                      ("name", Json.str typeDecl.userName.toString),
                      ("used", Json.bool used),
                      ("type", Json.str (Std.Format.pretty typePretty))
                    ]
                pure <| Json.mkObj [
                  ("module", Json.str target.moduleName),
                  ("requested_name", Json.str target.rawName),
                  ("name", Json.str declName.toString),
                  ("premises", Json.arr premises)
                ]
      | _ =>
          return Json.mkObj [
            ("module", Json.str target.moduleName),
            ("requested_name", Json.str target.rawName),
            ("name", Json.str declName.toString),
            ("error", Json.str "constant is not a theorem"),
            ("premises", Json.arr #[])
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
theorem canary_unused (a b : Nat) (h : a = b) : True := trivial
theorem canary_used (a b : Nat) (h : a = b) : b = a := h.symm
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
        premises = row.get("premises", [])
        unused = [
            premise.get("name", "<anonymous>")
            for premise in premises
            if premise.get("used") is False
        ]
        if premises and unused:
            candidates.append(
                {
                    "name": row.get("name", row.get("requested_name", "")),
                    "module": row.get("module", ""),
                    "unused_premises": unused,
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
        Target("_canary", "canary_unused"),
        Target("_canary", "canary_used"),
    ]
    results, _log = run_lean(targets, canary=True)
    by_requested = {row.get("requested_name"): row for row in results}
    unused = by_requested.get("canary_unused", {}).get("premises", [])
    used = by_requested.get("canary_used", {}).get("premises", [])
    unused_h = [premise for premise in unused if premise.get("name") == "h"]
    used_h = [premise for premise in used if premise.get("name") == "h"]
    passed = (
        len(unused_h) == 1
        and unused_h[0].get("used") is False
        and len(used_h) == 1
        and used_h[0].get("used") is True
    )
    out = make_output(
        results,
        "self-test canaries check proof-body fvar occurrence: canary_unused.h must be unused; canary_used.h must be used.",
        {"self_test": "PASS" if passed else "FAIL"},
    )
    print(json.dumps(out, ensure_ascii=False, indent=2))
    return 0 if passed else 1


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Informational Lean proof-term premise-insensitivity probe."
    )
    parser.add_argument(
        "--targets",
        help="comma-separated module:name targets; default uses a small pilot list",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="exit 1 when any eligible premise is unused",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run canary theorems and fail unless the detector distinguishes used from unused premises",
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
            "informational only: candidates have at least one explicit Prop premise whose proof binder does not occur in the theorem proof body; --strict turns candidates into exit 1.",
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
            "error": str(exc),
            "_note": "semantic_admission_probe failed before producing a sound audit result.",
        }
        print(json.dumps(out, ensure_ascii=False, indent=2))
        return 2


if __name__ == "__main__":
    sys.exit(main())
