import BEDC.Meta.DiscoveryCertificate
import BEDC.Meta.DiscoveryCertificateExample

namespace BEDC.Meta.DiscoveryDeltaLedger

open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.DiscoveryCertificate
open BEDC.Meta.DiscoveryCertificateExample
open BEDC.Meta.TasteGate

/-- Existential package for a concrete classifier displacement.

Static chapters leave this package absent. Discovery-bearing chapters fill it
with the full before/after `StructuralDiscovery` certificate. -/
structure DiscoveryShift where
  BeforeSource : BHist -> Prop
  BeforePattern : BHist -> Prop
  BeforeStability : BHist -> Prop
  BeforeLedger : BHist -> Prop
  BeforeClassifier : BHist -> BHist -> Prop
  AfterSource : BHist -> Prop
  AfterPattern : BHist -> Prop
  AfterStability : BHist -> Prop
  AfterLedger : BHist -> Prop
  AfterClassifier : BHist -> BHist -> Prop
  discovery :
    StructuralDiscovery
      BeforeSource BeforePattern BeforeStability BeforeLedger BeforeClassifier
      AfterSource AfterPattern AfterStability AfterLedger AfterClassifier

/-- Per-chapter ledger for after-state discovery accounting.

Every chapter carries the admission gate and row inventory. A classifier shift is
present only when the chapter records an actual before/after displacement. -/
structure DiscoveryDeltaLedger (X : Type) [BHistCarrier X] where
  admission : ChapterTasteGate X
  introduced_rows : Nat
  refusal_rows : Nat
  bridge_rows : Nat
  not_claimed_rows : Nat
  classifier_shift : Option DiscoveryShift

def ledgerBenefit {X : Type} [BHistCarrier X] (ledger : DiscoveryDeltaLedger X) : Nat :=
  ledger.introduced_rows + ledger.refusal_rows

def ledgerCost {X : Type} [BHistCarrier X] (ledger : DiscoveryDeltaLedger X) : Nat :=
  ledger.bridge_rows

def ledgerDebt {X : Type} [BHistCarrier X] (ledger : DiscoveryDeltaLedger X) : Nat :=
  ledger.not_claimed_rows

def ledgerScopeSeal {X : Type} [BHistCarrier X] (ledger : DiscoveryDeltaLedger X) : Nat :=
  match ledger.classifier_shift with
  | none => 0
  | some _ => 1

def ledgerPositiveMargin {X : Type} [BHistCarrier X] (ledger : DiscoveryDeltaLedger X) :
    Prop :=
  PositiveCostProtocol
    (ledgerBenefit ledger) (ledgerCost ledger) (ledgerDebt ledger) (ledgerScopeSeal ledger)

def ledgerDiscoveryCost {X : Type} [BHistCarrier X]
    (ledger : DiscoveryDeltaLedger X) (positive : ledgerPositiveMargin ledger) :
    DiscoveryCost where
  benefit := ledgerBenefit ledger
  cost := ledgerCost ledger
  debt := ledgerDebt ledger
  scopeSeal := ledgerScopeSeal ledger
  positive_margin := positive

theorem ledger_admission {X : Type} [BHistCarrier X] (ledger : DiscoveryDeltaLedger X) :
    ChapterTasteGate X := by
  exact ledger.admission

theorem ledger_round_trip {X : Type} [BHistCarrier X] (ledger : DiscoveryDeltaLedger X) :
    ∀ (x : X), BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x := by
  exact ledger.admission.round_trip

theorem ledgerDiscoveryCost_positive {X : Type} [BHistCarrier X]
    (ledger : DiscoveryDeltaLedger X) (positive : ledgerPositiveMargin ledger) :
    PositiveCostProtocol
      (ledgerDiscoveryCost ledger positive).benefit
      (ledgerDiscoveryCost ledger positive).cost
      (ledgerDiscoveryCost ledger positive).debt
      (ledgerDiscoveryCost ledger positive).scopeSeal := by
  exact costPositive (ledgerDiscoveryCost ledger positive)

theorem shiftedLedger_discoveryCost {X : Type} [BHistCarrier X]
    (ledger : DiscoveryDeltaLedger X) {shift : DiscoveryShift}
    (_present : ledger.classifier_shift = some shift)
    (positive : ledgerPositiveMargin ledger) :
    ∃ cost : DiscoveryCost,
      cost.benefit = ledgerBenefit ledger ∧
        cost.cost = ledgerCost ledger ∧
          cost.debt = ledgerDebt ledger ∧
            cost.scopeSeal = ledgerScopeSeal ledger ∧
              PositiveCostProtocol cost.benefit cost.cost cost.debt cost.scopeSeal := by
  exact
    Exists.intro
      (ledgerDiscoveryCost ledger positive)
      (And.intro rfl
        (And.intro rfl
          (And.intro rfl
            (And.intro rfl
              (ledgerDiscoveryCost_positive ledger positive)))))

theorem shiftedLedger_structuralDiscovery {X : Type} [BHistCarrier X]
    (ledger : DiscoveryDeltaLedger X) {shift : DiscoveryShift}
    (present : ledger.classifier_shift = some shift) :
    ∃ discovery :
      StructuralDiscovery
        shift.BeforeSource shift.BeforePattern shift.BeforeStability shift.BeforeLedger
        shift.BeforeClassifier shift.AfterSource shift.AfterPattern shift.AfterStability
        shift.AfterLedger shift.AfterClassifier,
      ledger.classifier_shift = some shift ∧ discovery = shift.discovery := by
  exact Exists.intro shift.discovery (And.intro present rfl)

theorem shiftedLedger_classifierNonEquivalent {X : Type} [BHistCarrier X]
    (ledger : DiscoveryDeltaLedger X) {shift : DiscoveryShift}
    (_present : ledger.classifier_shift = some shift) :
    ClassifierNonEquivalent
      shift.discovery.scope shift.BeforeSource shift.AfterSource
      shift.BeforeClassifier shift.AfterClassifier := by
  exact shift.discovery.classifier_shift

def smokeDiscoveryShift : DiscoveryShift where
  BeforeSource := SmokeSource
  BeforePattern := SmokeSource
  BeforeStability := SmokeSource
  BeforeLedger := SmokeSource
  BeforeClassifier := SmokeClassifierBefore
  AfterSource := SmokeSource
  AfterPattern := SmokeSource
  AfterStability := SmokeSource
  AfterLedger := SmokeSource
  AfterClassifier := SmokeClassifierAfter
  discovery := smokeStructuralDiscovery

local instance : BHistCarrier EventFlow :=
  groundCompilerBHistCarrier

def groundCompilerDeltaLedger : DiscoveryDeltaLedger EventFlow where
  admission := groundCompilerChapterTasteGate
  introduced_rows := 2
  refusal_rows := 1
  bridge_rows := 0
  not_claimed_rows := 0
  classifier_shift := none

theorem groundCompilerDeltaLedger_inhabited :
    Nonempty (DiscoveryDeltaLedger EventFlow) := by
  exact ⟨groundCompilerDeltaLedger⟩

theorem groundCompilerDeltaLedger_empty_roundTrip :
    @BHistCarrier.fromEventFlow EventFlow groundCompilerBHistCarrier
        (@BHistCarrier.toEventFlow EventFlow groundCompilerBHistCarrier ([] : EventFlow)) =
      some ([] : EventFlow) := by
  exact
    @ledger_round_trip EventFlow groundCompilerBHistCarrier
      groundCompilerDeltaLedger ([] : EventFlow)

def smokeShiftDeltaLedger : DiscoveryDeltaLedger EventFlow where
  admission := groundCompilerChapterTasteGate
  introduced_rows := 2
  refusal_rows := 1
  bridge_rows := 0
  not_claimed_rows := 0
  classifier_shift := some smokeDiscoveryShift

theorem smokeShiftDeltaLedger_margin :
    ledgerPositiveMargin smokeShiftDeltaLedger := by
  exact Nat.succ_lt_succ (Nat.zero_lt_succ 1)

theorem smokeShiftDeltaLedger_cost :
    ∃ cost : DiscoveryCost,
      PositiveCostProtocol cost.benefit cost.cost cost.debt cost.scopeSeal := by
  obtain ⟨cost, _benefit, _cost, _debt, _seal, positive⟩ :=
    shiftedLedger_discoveryCost
      smokeShiftDeltaLedger
      rfl
      smokeShiftDeltaLedger_margin
  exact ⟨cost, positive⟩

theorem smokeShiftDeltaLedger_classifierShift :
    ClassifierNonEquivalent
      smokeDiscoveryShift.discovery.scope
      smokeDiscoveryShift.BeforeSource
      smokeDiscoveryShift.AfterSource
      smokeDiscoveryShift.BeforeClassifier
      smokeDiscoveryShift.AfterClassifier := by
  exact shiftedLedger_classifierNonEquivalent smokeShiftDeltaLedger rfl

end BEDC.Meta.DiscoveryDeltaLedger
