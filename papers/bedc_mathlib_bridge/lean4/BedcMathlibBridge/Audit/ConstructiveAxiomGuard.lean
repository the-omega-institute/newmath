import BedcMathlibBridge.Constructive
import Lean

namespace BedcMathlibBridge.Audit.ConstructiveAxiomGuard

open Lean Elab Command

def constructivePrefix : Name :=
  `BedcMathlibBridge.Constructive

def forbiddenAxioms : List Name :=
  [`Classical.choice, `Quot.sound, `propext]

partial def hasGeneratedComponent : Name -> Bool
  | Name.anonymous => false
  | Name.str parent component =>
      component.startsWith "_" ||
        component.startsWith "match_" ||
        component.startsWith "proof_" ||
        hasGeneratedComponent parent
  | Name.num parent _ =>
      hasGeneratedComponent parent

def shouldAuditName (name : Name) : Bool :=
  constructivePrefix.isPrefixOf name &&
    !name.isInternal &&
    !name.hasMacroScopes &&
    !hasGeneratedComponent name

def forbiddenIn (axioms : Array Name) : List Name :=
  forbiddenAxioms.filter fun forbidden => axioms.contains forbidden

def formatNames (names : List Name) : MessageData :=
  match names with
  | [] => m!""
  | first :: rest =>
      rest.foldl (init := m!"{first}") fun acc name => m!"{acc}, {name}"

def formatArrayNames (names : Array Name) : MessageData :=
  formatNames names.toList

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut audited : Nat := 0
  for (name, _) in env.constants.toList do
    if shouldAuditName name then
      audited := audited + 1
      let axioms ← collectAxioms name
      let forbidden := forbiddenIn axioms
      unless axioms.isEmpty do
        let forbiddenMessage :=
          if forbidden.isEmpty then
            m!""
          else
            m!" forbidden subset: {formatNames forbidden}."
        throwError
          m!"constructive declaration {name} depends on axiom(s): {formatArrayNames axioms}.{forbiddenMessage}"
  logInfo m!"[bridge-axioms] audited {audited} constructive declaration(s)"

end BedcMathlibBridge.Audit.ConstructiveAxiomGuard
