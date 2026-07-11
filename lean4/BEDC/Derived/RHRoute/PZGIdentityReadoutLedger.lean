import BEDC.Derived.RHRoute.FinitePrimeTowerReadout
import BEDC.Derived.RHRoute.OCLSDPhaseAlgebra

namespace BEDC.Derived.RHRoute.PZGIdentityReadoutLedger

universe u v

open BEDC.Derived.RHRoute.OCLSDPhaseAlgebra

abbrev PrimeWindow := BEDC.Derived.RHRoute.FinitePrimeTowerReadout.PrimeWindow
abbrev FinitePrimeTower := BEDC.Derived.RHRoute.FinitePrimeTowerReadout.FinitePrimeTower
abbrev CompletedReadoutFor :=
  BEDC.Derived.RHRoute.FinitePrimeTowerReadout.CompletedReadoutFor

structure KernelCode where
  data : PZGRow
  rules : PZGRow
  ledger : PZGRow

structure KernelObject where
  data : PZGRow
  rules : PZGRow
  ledger : PZGRow

def Code (X : KernelObject) : KernelCode where
  data := X.data
  rules := X.rules
  ledger := X.ledger

theorem same_components_same_code {X Y : KernelObject}
    (data_eq : X.data = Y.data)
    (rules_eq : X.rules = Y.rules)
    (ledger_eq : X.ledger = Y.ledger) :
    Code X = Code Y := by
  cases X with
  | mk xData xRules xLedger =>
      cases Y with
      | mk yData yRules yLedger =>
          cases data_eq
          cases rules_eq
          cases ledger_eq
          rfl

theorem same_code_same_object {X Y : KernelObject} :
    Code X = Code Y -> X = Y := by
  intro code_eq
  cases X with
  | mk xData xRules xLedger =>
      cases Y with
      | mk yData yRules yLedger =>
          have data_eq : xData = yData := congrArg KernelCode.data code_eq
          have rules_eq : xRules = yRules := congrArg KernelCode.rules code_eq
          have ledger_eq : xLedger = yLedger := congrArg KernelCode.ledger code_eq
          cases data_eq
          cases rules_eq
          cases ledger_eq
          rfl

theorem no_hidden_register {X Y : KernelObject}
    (data_eq : X.data = Y.data)
    (rules_eq : X.rules = Y.rules)
    (ledger_eq : X.ledger = Y.ledger) :
    X = Y := by
  exact same_code_same_object
    (same_components_same_code data_eq rules_eq ledger_eq)

structure PZGCoordinate where
  prime : Nat
  index : Nat

def coordinateMatches (coord : PZGCoordinate) (prime index : Nat) : Bool :=
  if coord.prime = prime then
    if coord.index = index then true else false
  else
    false

def readCoordinate (coord : PZGCoordinate) : PZGRow -> Bool
  | PZGRow.nil => false
  | PZGRow.cons prime index rest =>
      if coordinateMatches coord prime index then
        true
      else
        readCoordinate coord rest

def readCoordinates : List PZGCoordinate -> PZGRow -> List Bool
  | [], _row => []
  | coord :: rest, row => readCoordinate coord row :: readCoordinates rest row

structure FiniteReadoutWindow where
  coordinates : List PZGCoordinate
  depth : Nat
  time : Nat
  epsilon : Nat

def R_W (window : FiniteReadoutWindow) (row : PZGRow) : List Bool :=
  readCoordinates window.coordinates row

def singletonWindow (coord : PZGCoordinate)
    (depth time epsilon : Nat) : FiniteReadoutWindow where
  coordinates := [coord]
  depth := depth
  time := time
  epsilon := epsilon

theorem coordinateMatches_self (coord : PZGCoordinate) :
    coordinateMatches coord coord.prime coord.index = true := by
  unfold coordinateMatches
  rw [if_pos rfl, if_pos rfl]

theorem readCoordinate_head (coord : PZGCoordinate) (rest : PZGRow) :
    readCoordinate coord (PZGRow.cons coord.prime coord.index rest) = true := by
  unfold readCoordinate
  rw [coordinateMatches_self coord]
  rw [if_pos rfl]

theorem readCoordinates_length :
    ∀ (coords : List PZGCoordinate) (row : PZGRow),
      (readCoordinates coords row).length = coords.length
  | [], _row => rfl
  | _coord :: rest, row => congrArg Nat.succ (readCoordinates_length rest row)

theorem finite_window_readout_length
    (window : FiniteReadoutWindow) (row : PZGRow) :
    (R_W window row).length = window.coordinates.length :=
  readCoordinates_length window.coordinates row

theorem singleton_window_readout (coord : PZGCoordinate)
    (depth time epsilon : Nat) (row : PZGRow) :
    R_W (singletonWindow coord depth time epsilon) row =
      [readCoordinate coord row] := rfl

theorem singleton_window_separates {coord : PZGCoordinate}
    {left right : PZGRow} {depth time epsilon : Nat} :
    readCoordinate coord left ≠ readCoordinate coord right ->
      R_W (singletonWindow coord depth time epsilon) left ≠
        R_W (singletonWindow coord depth time epsilon) right := by
  intro different sameReadout
  change [readCoordinate coord left] = [readCoordinate coord right] at sameReadout
  injection sameReadout with sameHead _sameTail
  exact different sameHead

theorem completed_prime_tower_readout_window_deterministic
    {tower : FinitePrimeTower} (left right : CompletedReadoutFor tower) :
    left.window.elems = right.window.elems :=
  BEDC.Derived.RHRoute.FinitePrimeTowerReadout.completed_readout_deterministic
    left right

inductive ResidualStatus where
  | openState : ResidualStatus
  | closedState : ResidualStatus
  | tailState : ResidualStatus
  | semanticState : ResidualStatus

theorem residual_status_exhaustive (status : ResidualStatus) :
    status = ResidualStatus.openState ∨
      status = ResidualStatus.closedState ∨
      status = ResidualStatus.tailState ∨
      status = ResidualStatus.semanticState := by
  cases status with
  | openState => exact Or.inl rfl
  | closedState => exact Or.inr (Or.inl rfl)
  | tailState => exact Or.inr (Or.inr (Or.inl rfl))
  | semanticState => exact Or.inr (Or.inr (Or.inr rfl))

structure ResidualDelta where
  expected : PZGRow
  actual : PZGRow

def residualClosed (delta : ResidualDelta) : Prop :=
  delta.expected = delta.actual

inductive ClosedResidualEvidence (delta : ResidualDelta) where
  | zero : residualClosed delta -> ClosedResidualEvidence delta
  | refutes : Not (residualClosed delta) -> ClosedResidualEvidence delta

structure LedgerEntry where
  source : PZGRow
  detector : PZGRow
  status : ResidualStatus
  next : PZGRow

def semanticLayerShift : PZGRow :=
  PZGRow.cons 0 0 PZGRow.nil

def semanticLedgerEntry (source detector : PZGRow) : LedgerEntry where
  source := source
  detector := detector
  status := ResidualStatus.semanticState
  next := semanticLayerShift

theorem semantic_entry_forces_layer_shift (source detector : PZGRow) :
    (semanticLedgerEntry source detector).status = ResidualStatus.semanticState ∧
      (semanticLedgerEntry source detector).next = semanticLayerShift :=
  And.intro rfl rfl

def tailLedgerEntry (source detector next : PZGRow) : LedgerEntry where
  source := source
  detector := detector
  status := ResidualStatus.tailState
  next := next

theorem tail_entry_status (source detector next : PZGRow) :
    (tailLedgerEntry source detector next).status = ResidualStatus.tailState :=
  rfl

inductive TailControl where
  | vanishing : TailControl
  | persistent : TailControl

def combineTailControl : TailControl -> TailControl -> TailControl
  | TailControl.vanishing, right =>
      match right with
      | TailControl.vanishing => TailControl.vanishing
      | TailControl.persistent => TailControl.persistent
  | TailControl.persistent, _right => TailControl.persistent

structure TailCert (family : Nat -> FiniteReadoutWindow) where
  budget : Nat -> Nat
  bound : Nat -> Type u
  control : TailControl

namespace TailCert

def add {family : Nat -> FiniteReadoutWindow}
    (left right : TailCert.{u} family) : TailCert.{u} family where
  budget := fun index => left.budget index + right.budget index
  bound := fun index => left.bound index × right.bound index
  control := combineTailControl left.control right.control

theorem add_budget {family : Nat -> FiniteReadoutWindow}
    (left right : TailCert.{u} family) (index : Nat) :
    (add left right).budget index =
      left.budget index + right.budget index := rfl

def add_bound_left {family : Nat -> FiniteReadoutWindow}
    (left right : TailCert.{u} family) (index : Nat) :
    (add left right).bound index -> left.bound index := by
  intro boundPair
  exact boundPair.1

def add_bound_right {family : Nat -> FiniteReadoutWindow}
    (left right : TailCert.{u} family) (index : Nat) :
    (add left right).bound index -> right.bound index := by
  intro boundPair
  exact boundPair.2

end TailCert

structure TailClosed where
  family : Nat -> FiniteReadoutWindow
  cert : TailCert.{u} family

theorem tail_closed_decomposes (closed : TailClosed.{u}) :
    ∃ family : Nat -> FiniteReadoutWindow, Nonempty (TailCert.{u} family) :=
  Exists.intro closed.family (Nonempty.intro closed.cert)

structure LedgerDiscipline (Obj : Type u) (Residual : Type v) where
  openLedger : Obj -> Residual -> Prop
  detectable : Obj -> Residual -> Prop
  detectable_enters :
    {object : Obj} -> {residual : Residual} ->
      detectable object residual -> openLedger object residual

theorem empty_open_ledger_no_detectable
    (discipline : LedgerDiscipline Obj Residual) {object : Obj} :
    (∀ residual : Residual, Not (discipline.openLedger object residual)) ->
      ∀ residual : Residual, Not (discipline.detectable object residual) := by
  intro emptyLedger residual detected
  exact emptyLedger residual (discipline.detectable_enters detected)

structure BoolReadoutCounterexample {α : Type u} (readout : α -> Bool) where
  witness : α
  reads_false : readout witness = false

theorem bool_readout_counterexample_refutes
    {α : Type u} {readout : α -> Bool}
    (counterexample : BoolReadoutCounterexample readout) :
    Not (∀ witness : α, readout witness = true) := by
  intro allTrue
  have readsTrue : readout counterexample.witness = true :=
    allTrue counterexample.witness
  rw [counterexample.reads_false] at readsTrue
  cases readsTrue

end BEDC.Derived.RHRoute.PZGIdentityReadoutLedger
