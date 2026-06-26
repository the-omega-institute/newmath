import BEDC.Derived.ContFracUp
import BEDC.Derived.PellUp

namespace BEDC.Derived.QuadraticSurdContFracUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)

abbrev NatWord := BHist
abbrev Z := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq := BEDC.Algebra.Rel.IntEq

def natOfLength (n : NatWord) : NatWord :=
  natToUnary (bwordLength n)

def natSquare (n : NatWord) : NatWord :=
  natToUnary (bwordLength n * bwordLength n)

def natMulWord (a b : NatWord) : NatWord :=
  natToUnary (bwordLength a * bwordLength b)

def natSubWord (a b : NatWord) : NatWord :=
  natToUnary (bwordLength a - bwordLength b)

def natDivWord (a b : NatWord) : NatWord :=
  match bwordLength b with
  | 0 => BHist.Empty
  | d + 1 => natToUnary (bwordLength a / (d + 1))

def natModWord (a b : NatWord) : NatWord :=
  match bwordLength b with
  | 0 => natOfLength a
  | d + 1 => natToUnary (bwordLength a % (d + 1))

theorem natOfLength_unary (n : NatWord) :
    UnaryHistory (natOfLength n) :=
  natToUnary_unary _

theorem natSquare_unary (n : NatWord) :
    UnaryHistory (natSquare n) :=
  natToUnary_unary _

theorem natMulWord_unary (a b : NatWord) :
    UnaryHistory (natMulWord a b) :=
  natToUnary_unary _

theorem natSubWord_unary (a b : NatWord) :
    UnaryHistory (natSubWord a b) :=
  natToUnary_unary _

theorem natDivWord_unary (a b : NatWord) :
    UnaryHistory (natDivWord a b) := by
  unfold natDivWord
  cases bwordLength b with
  | zero =>
      exact unary_empty
  | succ d =>
      exact natToUnary_unary _

theorem natModWord_unary (a b : NatWord) :
    UnaryHistory (natModWord a b) := by
  unfold natModWord
  cases bwordLength b with
  | zero =>
      exact natOfLength_unary a
  | succ d =>
      exact natToUnary_unary _

structure SqrtSurdState where
  P : NatWord
  Q : NatWord
  a : NatWord

def SqrtSurdStateCarrier (s : SqrtSurdState) : Prop :=
  UnaryHistory s.P ∧ UnaryHistory s.Q ∧ UnaryHistory s.a

def SqrtSurdStateEq
    (x y : SqrtSurdState) : Prop :=
  x.P = y.P ∧ x.Q = y.Q ∧ x.a = y.a

def surdNumerator (_a0 _P Q a : NatWord) : NatWord :=
  natMulWord Q a

def surdPNext (a0 P Q a : NatWord) : NatWord :=
  natSubWord (surdNumerator a0 P Q a) P

def surdRemainder (D P : NatWord) : NatWord :=
  natSubWord D (natSquare P)

def surdQNext (D P Q : NatWord) : NatWord :=
  natDivWord (surdRemainder D P) Q

def surdANext (a0 P Q : NatWord) : NatWord :=
  natDivWord (natToUnary (bwordLength a0 + bwordLength P)) Q

def sqrtInitialState (_D a0 : NatWord) : SqrtSurdState :=
  { P := BHist.Empty, Q := natToUnary 1, a := a0 }

def sqrtStep (D a0 : NatWord) (s : SqrtSurdState) :
    SqrtSurdState :=
  let Pnext := surdPNext a0 s.P s.Q s.a
  let Qnext := surdQNext D Pnext s.Q
  { P := Pnext, Q := Qnext, a := surdANext a0 Pnext Qnext }

theorem sqrtStep_P (D a0 : NatWord) (s : SqrtSurdState) :
    (sqrtStep D a0 s).P = surdPNext a0 s.P s.Q s.a := by
  rfl

theorem sqrtStep_Q (D a0 : NatWord) (s : SqrtSurdState) :
    (sqrtStep D a0 s).Q =
      surdQNext D (surdPNext a0 s.P s.Q s.a) s.Q := by
  rfl

theorem sqrtStep_a (D a0 : NatWord) (s : SqrtSurdState) :
    (sqrtStep D a0 s).a =
      surdANext a0 (surdPNext a0 s.P s.Q s.a)
        (surdQNext D (surdPNext a0 s.P s.Q s.a) s.Q) := by
  rfl

def sqrtStateAfter (D a0 : NatWord) :
    Nat -> SqrtSurdState -> SqrtSurdState
  | 0, s => s
  | n + 1, s => sqrtStateAfter D a0 n (sqrtStep D a0 s)

theorem sqrtStateAfter_zero (D a0 : NatWord)
    (s : SqrtSurdState) :
    sqrtStateAfter D a0 0 s = s := by
  rfl

theorem sqrtStateAfter_succ (D a0 : NatWord) (n : Nat)
    (s : SqrtSurdState) :
    sqrtStateAfter D a0 (n + 1) s =
      sqrtStateAfter D a0 n (sqrtStep D a0 s) := by
  rfl

def sqrtState (D a0 : NatWord) (n : Nat) : SqrtSurdState :=
  sqrtStateAfter D a0 n (sqrtInitialState D a0)

theorem sqrtState_zero (D a0 : NatWord) :
    sqrtState D a0 0 = sqrtInitialState D a0 := by
  rfl

def sqrtCoeff (D a0 : NatWord) (n : Nat) : NatWord :=
  (sqrtState D a0 n).a

def sqrtStatesFrom (D a0 : NatWord) :
    Nat -> SqrtSurdState -> List SqrtSurdState
  | 0, s => [s]
  | n + 1, s => s :: sqrtStatesFrom D a0 n (sqrtStep D a0 s)

def sqrtStates (D a0 : NatWord) (fuel : Nat) :
    List SqrtSurdState :=
  sqrtStatesFrom D a0 fuel (sqrtInitialState D a0)

def sqrtCoeffsFrom (D a0 : NatWord) :
    Nat -> SqrtSurdState -> List NatWord
  | 0, s => [s.a]
  | n + 1, s => s.a :: sqrtCoeffsFrom D a0 n (sqrtStep D a0 s)

def sqrtCoeffs (D a0 : NatWord) (fuel : Nat) : List NatWord :=
  sqrtCoeffsFrom D a0 fuel (sqrtInitialState D a0)

theorem sqrtInitialState_carrier (D a0 : NatWord) :
    UnaryHistory a0 ->
      SqrtSurdStateCarrier (sqrtInitialState D a0) := by
  intro a0Unary
  unfold SqrtSurdStateCarrier sqrtInitialState
  exact ⟨unary_empty, natToUnary_unary 1, a0Unary⟩

theorem sqrtStep_carrier (D a0 : NatWord) (s : SqrtSurdState) :
    SqrtSurdStateCarrier s ->
      SqrtSurdStateCarrier (sqrtStep D a0 s) := by
  intro _carrier
  unfold SqrtSurdStateCarrier sqrtStep surdPNext surdQNext
    surdANext surdNumerator surdRemainder
  exact ⟨natSubWord_unary _ _, natDivWord_unary _ _, natDivWord_unary _ _⟩

theorem sqrtStateAfter_carrier (D a0 : NatWord) (n : Nat)
    (s : SqrtSurdState) :
    SqrtSurdStateCarrier s ->
      SqrtSurdStateCarrier (sqrtStateAfter D a0 n s) := by
  intro carrier
  induction n generalizing s with
  | zero =>
      exact carrier
  | succ n ih =>
      exact ih (sqrtStep D a0 s) (sqrtStep_carrier D a0 s carrier)

theorem sqrtState_carrier (D a0 : NatWord) (n : Nat) :
    UnaryHistory a0 ->
      SqrtSurdStateCarrier (sqrtState D a0 n) := by
  intro a0Unary
  unfold sqrtState
  exact sqrtStateAfter_carrier D a0 n (sqrtInitialState D a0)
    (sqrtInitialState_carrier D a0 a0Unary)

theorem sqrtStatesFrom_length (D a0 : NatWord) (fuel : Nat)
    (s : SqrtSurdState) :
    (sqrtStatesFrom D a0 fuel s).length = fuel + 1 := by
  induction fuel generalizing s with
  | zero =>
      rfl
  | succ fuel ih =>
      unfold sqrtStatesFrom
      change Nat.succ
          ((sqrtStatesFrom D a0 fuel (sqrtStep D a0 s)).length) =
        fuel + 1 + 1
      rw [ih (sqrtStep D a0 s)]

theorem sqrtStates_length (D a0 : NatWord) (fuel : Nat) :
    (sqrtStates D a0 fuel).length = fuel + 1 := by
  unfold sqrtStates
  exact sqrtStatesFrom_length D a0 fuel (sqrtInitialState D a0)

theorem sqrtCoeffsFrom_length (D a0 : NatWord) (fuel : Nat)
    (s : SqrtSurdState) :
    (sqrtCoeffsFrom D a0 fuel s).length = fuel + 1 := by
  induction fuel generalizing s with
  | zero =>
      rfl
  | succ fuel ih =>
      unfold sqrtCoeffsFrom
      change Nat.succ
          ((sqrtCoeffsFrom D a0 fuel (sqrtStep D a0 s)).length) =
        fuel + 1 + 1
      rw [ih (sqrtStep D a0 s)]

theorem sqrtCoeffs_length (D a0 : NatWord) (fuel : Nat) :
    (sqrtCoeffs D a0 fuel).length = fuel + 1 := by
  unfold sqrtCoeffs
  exact sqrtCoeffsFrom_length D a0 fuel (sqrtInitialState D a0)

theorem sqrtStatesFrom_all_carrier (D a0 : NatWord) (fuel : Nat)
    (s : SqrtSurdState) :
    SqrtSurdStateCarrier s ->
      ∀ t : SqrtSurdState, t ∈ sqrtStatesFrom D a0 fuel s ->
        SqrtSurdStateCarrier t := by
  intro carrier t mem
  induction fuel generalizing s with
  | zero =>
      unfold sqrtStatesFrom at mem
      cases mem with
      | head => exact carrier
      | tail _ impossible => cases impossible
  | succ fuel ih =>
      unfold sqrtStatesFrom at mem
      cases mem with
      | head => exact carrier
      | tail _ tailMem =>
          exact ih (sqrtStep D a0 s)
            (sqrtStep_carrier D a0 s carrier) tailMem

theorem sqrtStates_all_carrier (D a0 : NatWord) (fuel : Nat) :
    UnaryHistory a0 ->
      ∀ t : SqrtSurdState, t ∈ sqrtStates D a0 fuel ->
        SqrtSurdStateCarrier t := by
  intro a0Unary t mem
  unfold sqrtStates at mem
  exact sqrtStatesFrom_all_carrier D a0 fuel (sqrtInitialState D a0)
    (sqrtInitialState_carrier D a0 a0Unary) t mem

structure CompleteSurdFiniteBound (D a0 : NatWord) (fuel : Nat) where
  state_count : (sqrtStates D a0 fuel).length = fuel + 1
  coeff_count : (sqrtCoeffs D a0 fuel).length = fuel + 1
  all_state_carrier :
    ∀ t : SqrtSurdState, t ∈ sqrtStates D a0 fuel ->
      SqrtSurdStateCarrier t

theorem sqrtSurdStates_finite_bound (D a0 : NatWord) (fuel : Nat) :
    UnaryHistory a0 -> CompleteSurdFiniteBound D a0 fuel := by
  intro a0Unary
  exact
    { state_count := sqrtStates_length D a0 fuel
      coeff_count := sqrtCoeffs_length D a0 fuel
      all_state_carrier := sqrtStates_all_carrier D a0 fuel a0Unary }

def pComponents : List SqrtSurdState -> List NatWord
  | [] => []
  | s :: tail => s.P :: pComponents tail

def qComponents : List SqrtSurdState -> List NatWord
  | [] => []
  | s :: tail => s.Q :: qComponents tail

def aComponents : List SqrtSurdState -> List NatWord
  | [] => []
  | s :: tail => s.a :: aComponents tail

theorem pComponents_contains :
    ∀ {states : List SqrtSurdState} {s : SqrtSurdState},
      s ∈ states -> s.P ∈ pComponents states
  | [], _s, mem => by
      cases mem
  | first :: tail, _s, mem => by
      unfold pComponents
      cases mem with
      | head =>
          exact List.Mem.head (pComponents tail)
      | tail _ tailMem =>
          exact List.Mem.tail first.P (pComponents_contains tailMem)

theorem qComponents_contains :
    ∀ {states : List SqrtSurdState} {s : SqrtSurdState},
      s ∈ states -> s.Q ∈ qComponents states
  | [], _s, mem => by
      cases mem
  | first :: tail, _s, mem => by
      unfold qComponents
      cases mem with
      | head =>
          exact List.Mem.head (qComponents tail)
      | tail _ tailMem =>
          exact List.Mem.tail first.Q (qComponents_contains tailMem)

theorem aComponents_contains :
    ∀ {states : List SqrtSurdState} {s : SqrtSurdState},
      s ∈ states -> s.a ∈ aComponents states
  | [], _s, mem => by
      cases mem
  | first :: tail, _s, mem => by
      unfold aComponents
      cases mem with
      | head =>
          exact List.Mem.head (aComponents tail)
      | tail _ tailMem =>
          exact List.Mem.tail first.a (aComponents_contains tailMem)

structure CompleteSurdWindowBound (D a0 : NatWord) (fuel : Nat) where
  finite : CompleteSurdFiniteBound D a0 fuel
  P_bound : ∀ s : SqrtSurdState, s ∈ sqrtStates D a0 fuel ->
    s.P ∈ pComponents (sqrtStates D a0 fuel)
  Q_bound : ∀ s : SqrtSurdState, s ∈ sqrtStates D a0 fuel ->
    s.Q ∈ qComponents (sqrtStates D a0 fuel)
  a_bound : ∀ s : SqrtSurdState, s ∈ sqrtStates D a0 fuel ->
    s.a ∈ aComponents (sqrtStates D a0 fuel)

theorem sqrtSurdStates_window_bound
    (D a0 : NatWord) (fuel : Nat) :
    UnaryHistory a0 -> CompleteSurdWindowBound D a0 fuel := by
  intro a0Unary
  exact
    { finite := sqrtSurdStates_finite_bound D a0 fuel a0Unary
      P_bound := fun s mem => pComponents_contains mem
      Q_bound := fun s mem => qComponents_contains mem
      a_bound := fun s mem => aComponents_contains mem }

private theorem boolAnd_true_left {a b : Bool} :
    Bool.and a b = true -> a = true := by
  cases a <;> cases b <;> intro h <;> cases h <;> rfl

private theorem boolAnd_true_right {a b : Bool} :
    Bool.and a b = true -> b = true := by
  cases a <;> cases b <;> intro h <;> cases h <;> rfl

def stateEqBool (x y : SqrtSurdState) : Bool :=
  Bool.and
    (Bool.and (decide (x.P = y.P)) (decide (x.Q = y.Q)))
    (decide (x.a = y.a))

theorem stateEqBool_true :
    stateEqBool x y = true -> SqrtSurdStateEq x y := by
  intro h
  unfold stateEqBool at h
  have leftPair :
      Bool.and (decide (x.P = y.P)) (decide (x.Q = y.Q)) = true :=
    boolAnd_true_left h
  have aEqBool : decide (x.a = y.a) = true :=
    boolAnd_true_right h
  have pEqBool : decide (x.P = y.P) = true :=
    boolAnd_true_left leftPair
  have qEqBool : decide (x.Q = y.Q) = true :=
    boolAnd_true_right leftPair
  exact
    ⟨of_decide_eq_true pEqBool,
      of_decide_eq_true qEqBool,
      of_decide_eq_true aEqBool⟩

def firstRepeatAgainst :
    SqrtSurdState -> Nat -> List SqrtSurdState -> Option Nat
  | _s, _offset, [] => none
  | s, offset, t :: tail =>
      if stateEqBool s t then some offset
      else firstRepeatAgainst s (offset + 1) tail

def firstRepeat :
    Nat -> List SqrtSurdState -> Option (Nat × Nat)
  | _base, [] => none
  | base, s :: tail =>
      match firstRepeatAgainst s (base + 1) tail with
      | some j => some (base, j)
      | none => firstRepeat (base + 1) tail

def sqrtPeriodSearch (D a0 : NatWord) (fuel : Nat) :
    Option (Nat × Nat) :=
  firstRepeat 0 (sqrtStates D a0 fuel)

def getState? : Nat -> List SqrtSurdState -> Option SqrtSurdState
  | _n, [] => none
  | 0, s :: _tail => some s
  | n + 1, _s :: tail => getState? n tail

structure PeriodHit (D a0 : NatWord) (fuel : Nat) where
  start : Nat
  stop : Nat
  start_state : SqrtSurdState
  stop_state : SqrtSurdState
  start_lookup : getState? start (sqrtStates D a0 fuel) = some start_state
  stop_lookup : getState? stop (sqrtStates D a0 fuel) = some stop_state
  same_state : SqrtSurdStateEq start_state stop_state

private theorem firstRepeatAgainst_sound
    {s : SqrtSurdState} {offset : Nat}
    {tail : List SqrtSurdState} {j : Nat} :
    firstRepeatAgainst s offset tail = some j ->
      ∃ t : SqrtSurdState, t ∈ tail ∧ SqrtSurdStateEq s t := by
  intro h
  induction tail generalizing offset with
  | nil =>
      unfold firstRepeatAgainst at h
      cases h
  | cons t rest ih =>
      unfold firstRepeatAgainst at h
      by_cases same : stateEqBool s t = true
      · rw [if_pos same] at h
        cases h
        exact ⟨t, List.Mem.head rest, stateEqBool_true same⟩
      · rw [if_neg same] at h
        cases ih h with
        | intro u data =>
            exact ⟨u, List.Mem.tail t data.left, data.right⟩

theorem firstRepeat_sound
    {base : Nat} {states : List SqrtSurdState} {i j : Nat} :
    firstRepeat base states = some (i, j) ->
      ∃ s t : SqrtSurdState,
        s ∈ states ∧ t ∈ states ∧ SqrtSurdStateEq s t := by
  intro h
  induction states generalizing base with
  | nil =>
      unfold firstRepeat at h
      cases h
  | cons s tail ih =>
      unfold firstRepeat at h
      cases scan : firstRepeatAgainst s (base + 1) tail with
      | some hit =>
          rw [scan] at h
          cases h
          cases firstRepeatAgainst_sound scan with
          | intro t data =>
              exact ⟨s, t, List.Mem.head tail, List.Mem.tail s data.left, data.right⟩
      | none =>
          rw [scan] at h
          cases ih h with
          | intro u rest =>
              cases rest with
              | intro v data =>
                  exact ⟨u, v, List.Mem.tail s data.left,
                    List.Mem.tail s data.right.left, data.right.right⟩

theorem sqrtPeriodSearch_sound
    {D a0 : NatWord} {fuel i j : Nat} :
    sqrtPeriodSearch D a0 fuel = some (i, j) ->
      ∃ s t : SqrtSurdState,
        s ∈ sqrtStates D a0 fuel ∧ t ∈ sqrtStates D a0 fuel ∧
          SqrtSurdStateEq s t := by
  intro h
  unfold sqrtPeriodSearch at h
  exact firstRepeat_sound h

def stateAt (D a0 : NatWord) (n : Nat) :
    SqrtSurdState :=
  sqrtState D a0 n

theorem sqrtStatesFrom_get_zero (D a0 : NatWord) (fuel : Nat)
    (s : SqrtSurdState) :
    getState? 0 (sqrtStatesFrom D a0 fuel s) = some s := by
  cases fuel <;> rfl

theorem sqrtStatesFrom_get_succ (D a0 : NatWord) (fuel n : Nat)
    (s : SqrtSurdState) :
    getState? (n + 1) (sqrtStatesFrom D a0 (fuel + 1) s) =
      getState? n (sqrtStatesFrom D a0 fuel (sqrtStep D a0 s)) := by
  rfl

def PeriodicOnWindow (D a0 : NatWord) (start period fuel : Nat) : Prop :=
  ∀ n : Nat, start + n + period ≤ fuel ->
    SqrtSurdStateEq
      (sqrtState D a0 (start + n))
      (sqrtState D a0 (start + n + period))

structure EventuallyPeriodicWitness (D a0 : NatWord) where
  start : Nat
  period : Nat
  nonzero_period : period = 0 -> False
  window : Nat
  periodic_on_window : PeriodicOnWindow D a0 start period window

structure LagrangeFiniteCertificate (D a0 : NatWord) where
  fuel : Nat
  bound : CompleteSurdWindowBound D a0 fuel
  period : PeriodHit D a0 fuel

structure PellFromPeriodCandidate (D : Z) where
  coeffs : List Z
  convergent : BEDC.Derived.ContFracUp.ConvergentState Z
  pair : BEDC.Derived.PellUp.PellPair
  state_eq :
    BEDC.Derived.ContFracUp.integerConvergentStateOfList coeffs = convergent
  x_readback : Zeq pair.x convergent.curr.p
  y_readback : Zeq pair.y convergent.curr.q

structure PellPeriodLink (D : Z) where
  candidate : PellFromPeriodCandidate D
  pell_solution : BEDC.Derived.PellUp.IsPellSolution D
    candidate.pair.x candidate.pair.y

def pellLinkToSolution {D : Z} (link : PellPeriodLink D) :
    BEDC.Derived.PellUp.PellSolution D :=
  { x := link.candidate.pair.x
    y := link.candidate.pair.y
    isPell := link.pell_solution }

def sqrtPeriodToPellSolution {D : Z}
    (link : PellPeriodLink D) :
    BEDC.Derived.PellUp.IsPellSolution D
      (pellLinkToSolution link).x (pellLinkToSolution link).y :=
  link.pell_solution

theorem pellPeriodLink_solution_is_pell {D : Z}
    (link : PellPeriodLink D) :
    BEDC.Derived.PellUp.IsPellSolution D
      (pellLinkToSolution link).x (pellLinkToSolution link).y := by
  exact link.pell_solution

theorem sqrtCoeffs_integer_convergent_det
    (coeffs : List Z) :
    Zeq
      (BEDC.Derived.ContFracUp.integerConvergentDet
        (BEDC.Derived.ContFracUp.integerConvergentStateOfList coeffs))
      (BEDC.Derived.ContFracUp.Rel.alternatingOne
        BEDC.Algebra.Rel.IntegerUp_RelCommRing coeffs.length) :=
  BEDC.Derived.ContFracUp.integerContFracConvergents_det coeffs

def libraryComparisonSurface : List String :=
  ["continued fractions basic",
   "number theory Pell"]

end BEDC.Derived.QuadraticSurdContFracUp
