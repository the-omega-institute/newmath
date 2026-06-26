import BEDC.Derived.GoldenMeanShiftUp
import BEDC.Derived.RHRoute.RecursiveTower

namespace BEDC.Derived.RHRoute.NonfixedOrbit

universe u

def iterate {α : Type u} (step : α -> α) : Nat -> α -> α
  | 0, x => x
  | Nat.succ n, x => iterate step n (step x)

def orbitPrefix {α : Type u} (step : α -> α) (seed : α) : Nat -> List α
  | 0 => [seed]
  | Nat.succ n => seed :: orbitPrefix step (step seed) n

structure FiniteOrbit {α : Type u} (step : α -> α) (points : List α) where
  seed : α
  fuel : Nat
  points_eq : points = orbitPrefix step seed fuel

def IsNonfixed {α : Type u} (step : α -> α) (points : List α) : Prop :=
  (x : α) -> x ∈ points -> step x ≠ x

structure PeriodicOrbit {α : Type u} (step : α -> α) (points : List α) where
  seed : α
  period : Nat
  period_positive : period ≠ 0
  closes : iterate step period seed = seed
  points_eq : points = orbitPrefix step seed period

structure FiniteShiftMap (α : Type u) where
  support : List α
  step : α -> α
  closed : (x : α) -> x ∈ support -> step x ∈ support

structure SupportedFiniteOrbit {α : Type u} (M : FiniteShiftMap α) where
  points : List α
  finite : FiniteOrbit M.step points
  supported : (x : α) -> x ∈ points -> x ∈ M.support

def EnumeratedNonfixed {α : Type u} (M : FiniteShiftMap α) : Prop :=
  IsNonfixed M.step M.support

def nonfixedBool {α : Type u} [DecidableEq α] (step : α -> α) : List α -> Bool
  | [] => true
  | x :: xs => if step x = x then false else nonfixedBool step xs

def enumeratedNonfixedBool {α : Type u} [DecidableEq α] (M : FiniteShiftMap α) :
    Bool :=
  nonfixedBool M.step M.support

def orbitPrefix_finiteOrbit {α : Type u} (step : α -> α) (seed : α)
    (fuel : Nat) :
    FiniteOrbit step (orbitPrefix step seed fuel) := by
  exact ⟨seed, fuel, rfl⟩

theorem orbitPrefix_seed_mem {α : Type u} (step : α -> α) (seed : α)
    (fuel : Nat) :
    seed ∈ orbitPrefix step seed fuel := by
  cases fuel with
  | zero =>
      exact List.Mem.head []
  | succ n =>
      exact List.Mem.head (orbitPrefix step (step seed) n)

theorem finiteOrbit_seed_mem {α : Type u} {step : α -> α} {points : List α}
    (orbit : FiniteOrbit step points) :
    orbit.seed ∈ points := by
  cases orbit with
  | mk seed fuel points_eq =>
      cases points_eq
      exact orbitPrefix_seed_mem step seed fuel

def periodicOrbit_finite {α : Type u} {step : α -> α} {points : List α} :
    PeriodicOrbit step points -> FiniteOrbit step points := by
  intro orbit
  exact ⟨orbit.seed, orbit.period, orbit.points_eq⟩

theorem nonfixed_excludes_fixed_member {α : Type u} {step : α -> α}
    {points : List α} :
    IsNonfixed step points -> (x : α) -> x ∈ points -> step x = x -> False := by
  intro nonfixed x member fixed
  exact nonfixed x member fixed

theorem fixed_member_refutes_nonfixed {α : Type u} {step : α -> α}
    {points : List α} {x : α} :
    x ∈ points -> step x = x -> Not (IsNonfixed step points) := by
  intro member fixed nonfixed
  exact nonfixed x member fixed

theorem periodicOrbit_nonfixed_seed_not_fixed {α : Type u} {step : α -> α}
    {points : List α} :
    (orbit : PeriodicOrbit step points) ->
      IsNonfixed step points -> step orbit.seed ≠ orbit.seed := by
  intro orbit nonfixed
  cases orbit with
  | mk seed period period_positive closes points_eq =>
      cases points_eq
      exact nonfixed seed (orbitPrefix_seed_mem step seed period)

theorem orbitPrefix_supported {α : Type u} (M : FiniteShiftMap α) :
    (fuel : Nat) -> (seed : α) -> seed ∈ M.support ->
      (x : α) -> x ∈ orbitPrefix M.step seed fuel -> x ∈ M.support
  | 0, seed, seedMember, x, member => by
      cases member with
      | head =>
          exact seedMember
      | tail _ tailMember =>
          cases tailMember
  | Nat.succ n, seed, seedMember, x, member => by
      cases member with
      | head =>
          exact seedMember
      | tail _ tailMember =>
          exact orbitPrefix_supported M n (M.step seed) (M.closed seed seedMember)
            x tailMember

def supportedOrbitPrefix {α : Type u} (M : FiniteShiftMap α) (seed : α)
    (fuel : Nat) (seedMember : seed ∈ M.support) : SupportedFiniteOrbit M :=
  {
    points := orbitPrefix M.step seed fuel
    finite := orbitPrefix_finiteOrbit M.step seed fuel
    supported := orbitPrefix_supported M fuel seed seedMember
  }

theorem supportedOrbit_nonfixed_of_enumeration {α : Type u}
    {M : FiniteShiftMap α} (orbit : SupportedFiniteOrbit M) :
    EnumeratedNonfixed M -> IsNonfixed M.step orbit.points := by
  intro enumerated x member
  exact enumerated x (orbit.supported x member)

theorem nonfixedBool_true {α : Type u} [DecidableEq α] {step : α -> α} :
    ∀ {points : List α}, nonfixedBool step points = true ->
      IsNonfixed step points
  | [], _h => by
      intro x member
      cases member
  | y :: ys, h => by
      intro x member
      unfold nonfixedBool at h
      by_cases fixedY : step y = y
      · rw [if_pos fixedY] at h
        cases h
      · rw [if_neg fixedY] at h
        cases member with
        | head =>
            exact fixedY
        | tail _ tailMember =>
            exact nonfixedBool_true h x tailMember

theorem nonfixedBool_of_isNonfixed {α : Type u} [DecidableEq α]
    {step : α -> α} :
    ∀ {points : List α}, IsNonfixed step points ->
      nonfixedBool step points = true
  | [], _nonfixed => rfl
  | y :: ys, nonfixed => by
      unfold nonfixedBool
      have fixedY : step y ≠ y := nonfixed y (List.Mem.head ys)
      rw [if_neg fixedY]
      exact nonfixedBool_of_isNonfixed
        (fun x member => nonfixed x (List.Mem.tail y member))

theorem nonfixedBool_true_iff {α : Type u} [DecidableEq α]
    (step : α -> α) (points : List α) :
    nonfixedBool step points = true ↔ IsNonfixed step points := by
  constructor
  · exact nonfixedBool_true
  · exact nonfixedBool_of_isNonfixed

theorem nonfixedBool_false_witness {α : Type u} [DecidableEq α]
    {step : α -> α} :
    ∀ {points : List α}, nonfixedBool step points = false ->
      ∃ x, x ∈ points ∧ step x = x
  | [], h => by
      cases h
  | y :: ys, h => by
      unfold nonfixedBool at h
      by_cases fixedY : step y = y
      · exact ⟨y, List.Mem.head ys, fixedY⟩
      · rw [if_neg fixedY] at h
        obtain ⟨x, member, fixedX⟩ := nonfixedBool_false_witness h
        exact ⟨x, List.Mem.tail y member, fixedX⟩

theorem nonfixedBool_false_of_fixed_mem {α : Type u} [DecidableEq α]
    {step : α -> α} {x : α} :
    ∀ {points : List α}, x ∈ points -> step x = x ->
      nonfixedBool step points = false
  | [], member, _fixed => by
      cases member
  | y :: ys, member, fixed => by
      unfold nonfixedBool
      by_cases fixedY : step y = y
      · rw [if_pos fixedY]
      · rw [if_neg fixedY]
        cases member with
        | head =>
            exact False.elim (fixedY fixed)
        | tail _ tailMember =>
            exact nonfixedBool_false_of_fixed_mem tailMember fixed

theorem enumeratedNonfixedBool_true {α : Type u} [DecidableEq α]
    (M : FiniteShiftMap α) :
    enumeratedNonfixedBool M = true -> EnumeratedNonfixed M := by
  intro h
  exact nonfixedBool_true h

theorem enumeratedNonfixedBool_of_nonfixed {α : Type u} [DecidableEq α]
    (M : FiniteShiftMap α) :
    EnumeratedNonfixed M -> enumeratedNonfixedBool M = true := by
  intro h
  exact nonfixedBool_of_isNonfixed h

theorem enumeratedNonfixedBool_false_witness {α : Type u} [DecidableEq α]
    (M : FiniteShiftMap α) :
    enumeratedNonfixedBool M = false ->
      ∃ x, x ∈ M.support ∧ M.step x = x := by
  intro h
  exact nonfixedBool_false_witness h

theorem supportedOrbit_nonfixed_of_decision {α : Type u} [DecidableEq α]
    {M : FiniteShiftMap α} (orbit : SupportedFiniteOrbit M) :
    enumeratedNonfixedBool M = true -> IsNonfixed M.step orbit.points := by
  intro h
  exact supportedOrbit_nonfixed_of_enumeration orbit
    (enumeratedNonfixedBool_true M h)

namespace GoldenMean

open BEDC.Derived.GoldenMeanShiftUp

abbrev GoldenSigmaFiniteOrbit (points : List GoldenSequence) : Type :=
  FiniteOrbit sigma points

abbrev GoldenSigmaNonfixed (points : List GoldenSequence) : Prop :=
  IsNonfixed sigma points

def goldenWindowNonfixedBool (points : List (List Bit)) : Bool :=
  nonfixedBool shiftLeft points

def GoldenWindowShiftMap (support : List (List Bit))
    (closed : (w : List Bit) -> w ∈ support -> shiftLeft w ∈ support) :
    FiniteShiftMap (List Bit) :=
  {
    support := support
    step := shiftLeft
    closed := closed
  }

def goldenSigma_finiteOrbit_prefix (seed : GoldenSequence) (fuel : Nat) :
    GoldenSigmaFiniteOrbit (orbitPrefix sigma seed fuel) := by
  exact orbitPrefix_finiteOrbit sigma seed fuel

theorem goldenSigma_preserves_allowed (x : GoldenSequence) :
    sequenceAllowed x -> sequenceAllowed (sigma x) := by
  exact sigma_preserves_sequenceAllowed x

theorem goldenSigma_nonfixed_periodic_seed_not_fixed
    {points : List GoldenSequence} :
    (orbit : PeriodicOrbit sigma points) ->
      GoldenSigmaNonfixed points -> sigma orbit.seed ≠ orbit.seed := by
  exact periodicOrbit_nonfixed_seed_not_fixed

theorem goldenWindowNonfixedBool_true (points : List (List Bit)) :
    goldenWindowNonfixedBool points = true -> IsNonfixed shiftLeft points := by
  intro h
  exact nonfixedBool_true h

theorem goldenWindowNonfixedBool_of_nonfixed (points : List (List Bit)) :
    IsNonfixed shiftLeft points -> goldenWindowNonfixedBool points = true := by
  intro h
  exact nonfixedBool_of_isNonfixed h

theorem goldenWindowNonfixedBool_false_witness (points : List (List Bit)) :
    goldenWindowNonfixedBool points = false ->
      ∃ w, w ∈ points ∧ shiftLeft w = w := by
  intro h
  exact nonfixedBool_false_witness h

end GoldenMean

end BEDC.Derived.RHRoute.NonfixedOrbit
