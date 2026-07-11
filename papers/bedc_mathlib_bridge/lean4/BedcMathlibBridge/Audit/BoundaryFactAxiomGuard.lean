import Lean
import Lean.Util.CollectAxioms
import BedcMathlibBridge.Boundary.BernoulliAxiomLedger
import BedcMathlibBridge.Boundary.RiemannZetaAxiomLedger
import BedcMathlibBridge.Export.IntProbe
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Data.Nat.Totient
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Schroder
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Fermat
import Mathlib.NumberTheory.FactorisationProperties
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Order.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace BedcMathlibBridge.Audit.BoundaryFactAxiomGuard

open Lean
open Lean.Elab.Command

inductive ChoiceStatus where
  | eliminated
  | principledIrreducible
  | unprobed
deriving BEq, Repr

inductive AxiomStatus where
  | eliminated
  | mathlibIntrinsic
  | structuralQuotient
  | principledIrreducible
  | unprobed
deriving BEq, Repr

inductive Place where
  | finiteP
  | infiniteArchimedean
  | objectBase
  | nA
deriving BEq, Repr

inductive Locatedness where
  | located
  | arbitrary
  | nA
deriving BEq, Repr

inductive QuotientStatus where
  | structuralQuotient
  | quotientFree
  | nA
deriving BEq, Repr

structure BoundaryExpectation where
  rowId : String
  mathlibDecl : Name
  mathlibFootprint : Array Name
  bedcIrreducibleDecl : Name
  bedcIrreducibleFootprint : Array Name
  choiceStatus : ChoiceStatus
  place : Place
  locatedness : Locatedness
  quotientStatus : QuotientStatus
  axiomStatus : Array (Name × AxiomStatus)

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

noncomputable def auditRealConditionallyCompleteLinearOrder :
    ConditionallyCompleteLinearOrder _root_.Real :=
  inferInstance

noncomputable def auditRealSupSet : SupSet _root_.Real :=
  inferInstance

/-!
Audit-only touchpoint for the mathlib Zeckendorf representation and equivalence.
-/
noncomputable def auditNatZeckendorfBoundary :
    (Nat → List Nat) × (Nat ≃ {l // List.IsZeckendorfRep l}) :=
  (Nat.zeckendorf, Nat.zeckendorfEquiv)

/-!
Audit-only touchpoint for the mathlib standard Bell number. `Nat.bell`'s
recurrence body and its only general characterization (`Nat.bell_succ`) are
stated as a `Finset.sum` over `Fin n.succ`; `Finset = Multiset = Quotient List`,
so even the bare `Nat.bell` definition inherits the `Quot.sound`/`propext`
footprint and `Classical.choice` from the mathlib big-operator layer. The BEDC
side has a quotient-free Bell presentation (`bellNumber` as a Stirling prefix
sum, plus a 0-axiom standard recurrence `bellNumberByRecurrence`), but bridging
it to `Nat.bell` would have to route through `Nat.bell_succ`, importing those
axioms; this row records only the mathlib-object axiom cost and exports no
axiom-bearing bridge theorem.
-/
noncomputable def auditNatBellBoundary : Nat → Nat :=
  Nat.bell

/-!
Audit-only touchpoint for mathlib's Fermat numbers. The BEDC side gives a
quotient-free tower recurrence and prefix-product relation; the host declaration
itself retains the proposition-extensionality footprint measured by this row.
-/
noncomputable def auditNatFermatNumberBoundary : Nat → Nat :=
  Nat.fermatNumber

/-!
Audit-only touchpoint for mathlib Mersenne numbers. The host declaration is
definitionally `2 ^ p - 1`, but its compiled declaration footprint contains
`propext`, so it remains a measured boundary object rather than a bridge export.
-/
noncomputable def auditMersenneBoundary : Nat → Nat :=
  _root_.mersenne

/-!
Audit-only touchpoint for mathlib's large and small Schroder numbers. Their
recursive surface is stated through `Finset.sum`, so the host declarations
inherit the finite-set quotient and choice footprint rather than yielding a
0-axiom readback target.
-/
noncomputable def auditNatSchroderBoundary : (Nat → Nat) × (Nat → Nat) :=
  (Nat.largeSchroder, Nat.smallSchroder)

/-!
Audit-only touchpoint for mathlib's partition-count carrier. The host count is
the cardinality of `Nat.Partition n`, whose finite enumeration is built through
multisets, compositions, and finite type machinery.
-/
noncomputable def auditNatPartitionCountBoundary (n : Nat) : Nat :=
  Fintype.card (Nat.Partition n)

noncomputable def auditNatBinaryMultinomialBoundary (a b : Nat) : Nat :=
  Nat.multinomial (Finset.univ : Finset (Fin 2)) ![a, b]

/-!
Audit-only touchpoints for mathlib's finite number-theoretic functions whose
carrier definitions route through `Finset`, `Finsupp`, or arithmetic-function
big-operator layers.
-/
noncomputable def auditNatTotientBoundary : Nat → Nat :=
  Nat.totient

noncomputable def auditNatDivisorsBoundary : Nat → Finset Nat :=
  Nat.divisors

noncomputable def auditNatHarmonicNumberBoundary : Nat → Rat :=
  _root_.harmonic

noncomputable def auditArithmeticFunctionCarmichaelBoundary :
    ArithmeticFunction Nat :=
  ArithmeticFunction.Carmichael

/-!
Audit-only touchpoint for the mathlib prime-power theorem surface at `2 ^ 2`.
The BEDC perfect-power packet has a quotient-free decision surface for the
same square, but the host prime-power proof route is measured separately.
-/
theorem auditNatPerfectPowerPrimeSquareBoundary :
    IsPrimePow ((2 : Nat) ^ 2) :=
  (Nat.Prime.isPrimePow Nat.prime_two).pow (by decide : 2 ≠ 0)

/-!
Audit-only touchpoint for mathlib's abundant-number predicate at `12`. BEDC
has a quotient-free sigma-profile certificate for the same value, but the host
predicate is stated through `properDivisors` and a `Finset` sum.
-/
theorem auditNatAbundantTwelveBoundary : Nat.Abundant 12 :=
  Nat.abundant_twelve

/-!
Audit-only touchpoint for mathlib's weird-number predicate at the standard
`70` witness. The predicate is stated through `properDivisors` and a
subset-sum existential over `Finset`, so the host declaration is boundary data.
-/
noncomputable def auditNatWeirdSeventyBoundary : Prop :=
  Nat.Weird 70

/--
Audit-only carrier touchpoint for mathlib `Real`. In the current mathlib
implementation, even declarations whose type merely exposes `Real` inherit the
Cauchy-completion footprint.
-/
def auditRealCarrier (x : _root_.Real) : _root_.Real :=
  x

/--
Located-shaped LUB data keeps the candidate point and both `IsLUB` obligations
as explicit fields. This is the verification shape used to measure the gap
between consuming a supplied supremum and synthesizing one through `sSup`.
-/
structure LocatedLUBData {α : Type u} [LE α] (s : Set α) where
  point : α
  upper : point ∈ upperBounds s
  least : point ∈ lowerBounds (upperBounds s)

def locatedIsLUBCore {α : Type u} [LE α] {s : Set α} (data : LocatedLUBData s) :
    IsLUB s data.point :=
  ⟨data.upper, data.least⟩

def auditRealLocatedIsLUB {s : Set _root_.Real} (data : LocatedLUBData s) :
    IsLUB s data.point :=
  locatedIsLUBCore data

noncomputable def auditPadicIntCommRing (p : Nat) [Fact p.Prime] : CommRing ℤ_[p] :=
  inferInstance

noncomputable def auditPadicField (p : Nat) [Fact p.Prime] : Field ℚ_[p] :=
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

def duplicateStatusKeys (xs : Array (Name × AxiomStatus)) : Array Name :=
  duplicateNames (xs.map (·.1))

def sameNameSet (xs ys : Array Name) : Bool :=
  xs.size == ys.size && xs.all (fun x => containsName ys x)

def forbiddenAxioms : Array Name := #[
  `sorryAx,
  `Lean.trustCompiler,
  `Lean.ofReduceBool,
  `Lean.ofReduceBool
]

def classicalChoice : Name :=
  `Classical.choice

def quotSound : Name :=
  `Quot.sound

def axiomStatus? (xs : Array (Name × AxiomStatus)) (x : Name) : Option AxiomStatus :=
  xs.findSome? fun entry =>
    if entry.1 == x then some entry.2 else none

def intersection (xs ys : Array Name) : Array Name :=
  xs.filter fun x => containsName ys x

def auditFootprint (rowId : String) (label : String) (decl : Name)
    (expectedAxioms : Array Name) : CommandElabM (Array Name) := do
  let env ← getEnv
  unless env.contains decl do
    throwError m!"BEDC_GATE_E_MISSING_DECL: row `{rowId}` names absent {label} declaration `{decl}`"
  let dupes := duplicateNames expectedAxioms
  unless dupes.isEmpty do
    throwError m!
      "BEDC_GATE_E_DUPLICATE_AXIOM: row `{rowId}` repeats expected {label} axiom(s): \
      {formatNames dupes}"
  let actual ← collectAxioms decl
  let actualSorted := actual.qsort Name.quickLt
  let expectedSorted := expectedAxioms.qsort Name.quickLt
  let forbiddenHit := intersection actualSorted forbiddenAxioms
  unless forbiddenHit.isEmpty do
    throwError m!
      "BEDC_GATE_E_FORBIDDEN_AXIOM: row `{rowId}` {label} declaration `{decl}` has \
      forbidden axiom(s): [{formatNames forbiddenHit}]"
  unless sameNameSet actualSorted expectedSorted do
    throwError m!
      "BEDC_GATE_E_AXIOM_MISMATCH: row `{rowId}` {label} declaration `{decl}` has \
      [{formatNames actualSorted}], expected [{formatNames expectedSorted}]"
  return actualSorted

def auditAxiomStatus (e : BoundaryExpectation)
    (irreducible : Array Name) : CommandElabM Unit := do
  let dupes := duplicateStatusKeys e.axiomStatus
  unless dupes.isEmpty do
    throwError m!
      "BEDC_GATE_E_DUPLICATE_AXIOM_STATUS: row `{e.rowId}` repeats axiom_status key(s): \
      {formatNames dupes}"
  for axName in irreducible do
    match axiomStatus? e.axiomStatus axName with
    | none =>
        throwError m!
          "BEDC_GATE_E_AXIOM_UNCLASSIFIED: row `{e.rowId}` records `{axName}` \
          in the BEDC-irreducible footprint without axiom_status"
    | some AxiomStatus.unprobed =>
        throwError m!
          "BEDC_GATE_E_AXIOM_UNCLASSIFIED: row `{e.rowId}` records `{axName}` \
          in the BEDC-irreducible footprint with `unprobed` axiom_status"
    | some AxiomStatus.eliminated =>
        throwError m!
          "BEDC_GATE_E_REDUCIBLE_AXIOM: row `{e.rowId}` records `{axName}` \
          in the BEDC-irreducible footprint despite `eliminated` axiom_status"
    | some AxiomStatus.mathlibIntrinsic => pure ()
    | some AxiomStatus.structuralQuotient => pure ()
    | some AxiomStatus.principledIrreducible => pure ()
  for entry in e.axiomStatus do
    if entry.2 == AxiomStatus.eliminated && containsName irreducible entry.1 then
      throwError m!
        "BEDC_GATE_E_REDUCIBLE_AXIOM: row `{e.rowId}` marks `{entry.1}` \
        `eliminated`, but the BEDC-irreducible footprint still contains it"

def auditOne (e : BoundaryExpectation) : CommandElabM Unit := do
  let mathlib ← auditFootprint e.rowId "mathlib" e.mathlibDecl e.mathlibFootprint
  let irreducible ←
    auditFootprint e.rowId "BEDC-irreducible" e.bedcIrreducibleDecl
      e.bedcIrreducibleFootprint
  auditAxiomStatus e irreducible
  if containsName irreducible classicalChoice &&
      e.choiceStatus != ChoiceStatus.principledIrreducible then
    throwError m!
      "BEDC_GATE_E_REDUCIBLE_CHOICE: row `{e.rowId}` records `Classical.choice` \
      in the BEDC-irreducible footprint without `principled_irreducible` status"
  if !containsName irreducible classicalChoice &&
      e.choiceStatus == ChoiceStatus.principledIrreducible then
    throwError m!
      "BEDC_GATE_E_CHOICE_STATUS_MISMATCH: row `{e.rowId}` is marked \
      `principled_irreducible`, but its BEDC-irreducible footprint has no \
      `Classical.choice`"
  if !containsName mathlib quotSound &&
      e.quotientStatus == QuotientStatus.structuralQuotient then
    throwError m!
      "BEDC_GATE_E_QUOTIENT_STATUS_MISMATCH: row `{e.rowId}` is marked \
      `structural_quotient`, but its mathlib footprint has no \
      `Quot.sound`"
  if containsName mathlib quotSound &&
      e.quotientStatus == QuotientStatus.quotientFree then
    throwError m!
      "BEDC_GATE_E_QUOTIENT_STATUS_MISMATCH: row `{e.rowId}` is marked \
      `quotient_free`, but its mathlib footprint has `Quot.sound`"

def audit (expected : Array BoundaryExpectation) : CommandElabM Unit := do
  for e in expected do
    auditOne e
  logInfo m!"[boundary-axioms] audited {expected.size} boundary declaration row(s)"

end BedcMathlibBridge.Audit.BoundaryFactAxiomGuard
