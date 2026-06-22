import Lean
import Lean.Util.CollectAxioms
import BedcMathlibBridge.Export.IntProbe
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Order.Basic

namespace BedcMathlibBridge.Audit.BoundaryFactAxiomGuard

open Lean
open Lean.Elab.Command

structure BoundaryExpectation where
  rowId : String
  decl : Name
  expectedAxioms : Array Name

/--
Audit-only names for synthesized Int instances that have no standalone mathlib
declaration after instance search specializes the generic projection.
-/
noncomputable def auditIntConditionallyCompleteLinearOrder :
    ConditionallyCompleteLinearOrder _root_.Int :=
  inferInstance

noncomputable def auditIntSupSet : SupSet _root_.Int :=
  inferInstance

noncomputable def auditIntInfSet : InfSet _root_.Int :=
  inferInstance

def formatNames (names : Array Name) : String :=
  String.intercalate ", " (names.toList.map Name.toString)

def containsName (xs : Array Name) (x : Name) : Bool :=
  xs.any fun y => y == x

def duplicateNames (xs : Array Name) : Array Name := Id.run do
  let mut seen : Array Name := #[]
  let mut dupes : Array Name := #[]
  for x in xs do
    if containsName seen x then
      unless containsName dupes x do
        dupes := dupes.push x
    else
      seen := seen.push x
  return dupes

def sameNameSet (xs ys : Array Name) : Bool :=
  xs.size == ys.size && xs.all (fun x => containsName ys x)

def forbiddenAxioms : Array Name := #[
  `sorryAx,
  `Lean.trustCompiler,
  `Lean.ofReduceBool,
  `Lean.ofReduceBool
]

def intersection (xs ys : Array Name) : Array Name :=
  xs.filter fun x => containsName ys x

def auditOne (e : BoundaryExpectation) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains e.decl do
    throwError m!"BEDC_GATE_E_MISSING_DECL: row `{e.rowId}` names absent declaration `{e.decl}`"
  let dupes := duplicateNames e.expectedAxioms
  unless dupes.isEmpty do
    throwError m!
      "BEDC_GATE_E_DUPLICATE_AXIOM: row `{e.rowId}` repeats expected axiom(s): \
      {formatNames dupes}"
  let actual ← collectAxioms e.decl
  let actualSorted := actual.qsort Name.quickLt
  let expectedSorted := e.expectedAxioms.qsort Name.quickLt
  let forbiddenHit := intersection actualSorted forbiddenAxioms
  unless forbiddenHit.isEmpty do
    throwError m!
      "BEDC_GATE_E_FORBIDDEN_AXIOM: row `{e.rowId}` declaration `{e.decl}` has \
      forbidden axiom(s): [{formatNames forbiddenHit}]"
  unless sameNameSet actualSorted expectedSorted do
    throwError m!
      "BEDC_GATE_E_AXIOM_MISMATCH: row `{e.rowId}` declaration `{e.decl}` has \
      [{formatNames actualSorted}], expected [{formatNames expectedSorted}]"

def audit (expected : Array BoundaryExpectation) : CommandElabM Unit := do
  let decls := expected.map (·.decl)
  let dupes := duplicateNames decls
  unless dupes.isEmpty do
    throwError m!
      "BEDC_GATE_E_DUPLICATE_BOUNDARY: duplicate boundary declaration(s): {formatNames dupes}"
  for e in expected do
    auditOne e
  logInfo m!"[boundary-axioms] audited {expected.size} boundary declaration row(s)"

end BedcMathlibBridge.Audit.BoundaryFactAxiomGuard
