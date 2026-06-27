import BEDC.Derived.FibonacciUp

namespace BEDC.Derived.PisanoPeriodUp

abbrev fib : Nat -> Nat :=
  BEDC.Derived.FibonacciUp.fib

structure FibModState where
  left : Nat
  right : Nat
deriving DecidableEq

def nextFibModState (n : Nat) (s : FibModState) : FibModState :=
  { left := s.right
    right := (s.left + s.right) % n }

def fibModState (n : Nat) : Nat -> FibModState
  | 0 =>
      { left := fib 0 % n
        right := fib 1 % n }
  | k + 1 => nextFibModState n (fibModState n k)

theorem fibModState_step (n t : Nat) :
    fibModState n (t + 1) = nextFibModState n (fibModState n t) := by
  rfl

def PisanoReturn (n k : Nat) : Prop :=
  0 < n ∧ 0 < k ∧ fibModState n k = fibModState n 0

def PisanoCycle (n k : Nat) : Prop :=
  0 < n ∧ 0 < k ∧ ∀ t : Nat, fibModState n (t + k) = fibModState n t

def PisanoPeriod (n k : Nat) : Prop :=
  PisanoCycle n k ∧
    ∀ j : Nat, 0 < j -> j < k -> fibModState n j ≠ fibModState n 0

def noReturnBeforeFrom (n j fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | f + 1 =>
      if fibModState n j = fibModState n 0 then
        false
      else
        noReturnBeforeFrom n (j + 1) f

def noReturnBefore (n k : Nat) : Bool :=
  noReturnBeforeFrom n 1 (k - 1)

theorem noReturnBeforeFrom_sound {n j fuel : Nat} :
    noReturnBeforeFrom n j fuel = true ->
      ∀ r : Nat, j ≤ r -> r < j + fuel ->
        fibModState n r ≠ fibModState n 0 := by
  intro checked
  induction fuel generalizing j with
  | zero =>
      intro r jLeR rLt eqState
      rw [Nat.add_zero] at rLt
      exact False.elim ((Nat.not_lt_of_ge jLeR) rLt)
  | succ fuel ih =>
      intro r jLeR rLt eqState
      unfold noReturnBeforeFrom at checked
      by_cases current : fibModState n j = fibModState n 0
      · rw [if_pos current] at checked
        cases checked
      · rw [if_neg current] at checked
        cases Nat.lt_or_ge r (j + 1) with
        | inl rLtSucc =>
            have notRLtJ : ¬r < j := Nat.not_lt_of_ge jLeR
            have rEqJ : r = j := Nat.eq_of_lt_succ_of_not_lt rLtSucc notRLtJ
            exact current (by rw [← rEqJ]; exact eqState)
        | inr succLeR =>
            exact ih checked r succLeR
              (by
                change r < j + (fuel + 1) at rLt
                change r < (j + 1) + fuel
                have boundShape : j + (fuel + 1) = (j + 1) + fuel := by
                  rw [Nat.add_comm fuel 1]
                  rw [← Nat.add_assoc]
                rw [boundShape] at rLt
                exact rLt)
              eqState

theorem noReturnBefore_sound {n k : Nat} :
    noReturnBefore n k = true ->
      ∀ r : Nat, 0 < r -> r < k -> fibModState n r ≠ fibModState n 0 := by
  intro checked r rPositive rLt eqState
  unfold noReturnBefore at checked
  cases k with
  | zero =>
      exact False.elim ((Nat.not_lt_zero r) rLt)
  | succ k =>
      exact noReturnBeforeFrom_sound checked r rPositive
        (by
          change r < k + 1 at rLt
          change r < 1 + k
          rw [Nat.add_comm] at rLt
          exact rLt)
        eqState

theorem pisano_cycle_of_return {n k : Nat} :
    PisanoReturn n k -> PisanoCycle n k := by
  intro ret
  refine ⟨ret.left, ret.right.left, ?_⟩
  intro t
  induction t with
  | zero =>
      rw [Nat.zero_add]
      exact ret.right.right
  | succ t ih =>
      calc
        fibModState n (Nat.succ t + k) =
            nextFibModState n (fibModState n (t + k)) := by
          rw [show Nat.succ t + k = (t + k) + 1 by
            rw [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 k, ← Nat.add_assoc]]
          exact fibModState_step n (t + k)
        _ = nextFibModState n (fibModState n t) := by
          rw [ih]
        _ = fibModState n (Nat.succ t) := by
          change nextFibModState n (fibModState n t) = fibModState n (t + 1)
          exact (fibModState_step n t).symm

theorem pisano_return_two : PisanoReturn 2 3 := by
  constructor
  · decide
  · constructor
    · decide
    · decide

theorem pisano_cycle_two : PisanoCycle 2 3 :=
  pisano_cycle_of_return pisano_return_two

theorem pisanoPeriod_two : PisanoPeriod 2 3 := by
  constructor
  · exact pisano_cycle_two
  · exact noReturnBefore_sound (by rfl)

theorem pisano_return_three : PisanoReturn 3 8 := by
  constructor
  · decide
  · constructor
    · decide
    · decide

theorem pisano_cycle_three : PisanoCycle 3 8 :=
  pisano_cycle_of_return pisano_return_three

theorem pisanoPeriod_three : PisanoPeriod 3 8 := by
  constructor
  · exact pisano_cycle_three
  · exact noReturnBefore_sound (by rfl)

theorem pisano_return_ten : PisanoReturn 10 60 := by
  constructor
  · decide
  · constructor
    · decide
    · decide

theorem pisano_cycle_ten : PisanoCycle 10 60 :=
  pisano_cycle_of_return pisano_return_ten

theorem pisanoPeriod_ten : PisanoPeriod 10 60 := by
  constructor
  · exact pisano_cycle_ten
  · exact noReturnBefore_sound (by rfl)

end BEDC.Derived.PisanoPeriodUp
