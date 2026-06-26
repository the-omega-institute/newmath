import BEDC.Derived.BellNumberUp
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.PolynomialUp.IntegerRing

namespace BEDC.Derived.TouchardPolyUp

abbrev stirlingSecond : Nat -> Nat -> Nat :=
  BEDC.Derived.StirlingUp.stirlingSecond

abbrev bellNumber : Nat -> Nat :=
  BEDC.Derived.BellNumberUp.bellNumber

abbrev binomial : Nat -> Nat -> Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C

def natPow (x : Nat) : Nat -> Nat
  | 0 => 1
  | Nat.succ n => x * natPow x n

def touchardCoeff (n k : Nat) : Nat :=
  stirlingSecond n k

def touchardPolyPrefix (n : Nat) : Nat -> List Nat
  | 0 => [touchardCoeff n 0]
  | Nat.succ k => touchardPolyPrefix n k ++ [touchardCoeff n (Nat.succ k)]

def touchardPoly (n : Nat) : List Nat :=
  touchardPolyPrefix n n

def touchardTerm (n x k : Nat) : Nat :=
  touchardCoeff n k * natPow x k

def touchardEvalPrefix (n x : Nat) : Nat -> Nat
  | 0 => touchardTerm n x 0
  | Nat.succ k => touchardEvalPrefix n x k + touchardTerm n x (Nat.succ k)

def touchardEval (n x : Nat) : Nat :=
  touchardEvalPrefix n x n

def touchardBEDCPoly (n : Nat) : BEDC.Derived.PolynomialUp.Poly :=
  (touchardPoly n).map BEDC.Derived.PolynomialUp.coeffOfNat

def touchardBinomialRecurrencePrefix (n x : Nat) : Nat -> Nat
  | 0 => binomial n 0 * touchardEval 0 x
  | Nat.succ k =>
      touchardBinomialRecurrencePrefix n x k +
        binomial n (Nat.succ k) * touchardEval (Nat.succ k) x

def touchardStirlingStepPrefix (n x : Nat) : Nat -> Nat
  | 0 =>
      ((1 * stirlingSecond n 1) + stirlingSecond n 0) * natPow x 0
  | Nat.succ k =>
      touchardStirlingStepPrefix n x k +
        ((Nat.succ (Nat.succ k) * stirlingSecond n (Nat.succ (Nat.succ k))) +
          stirlingSecond n (Nat.succ k)) * natPow x (Nat.succ k)

theorem natPow_zero_right (x : Nat) :
    natPow x 0 = 1 := by
  rfl

theorem natPow_succ (x k : Nat) :
    natPow x (Nat.succ k) = x * natPow x k := by
  rfl

theorem natPow_one :
    ∀ k : Nat, natPow 1 k = 1
  | 0 => rfl
  | Nat.succ k => by
      change 1 * natPow 1 k = 1
      rw [natPow_one k]

theorem touchardCoeff_definition (n k : Nat) :
    touchardCoeff n k = stirlingSecond n k := by
  rfl

theorem touchardPoly_zero :
    touchardPoly 0 = [1] := by
  rfl

theorem touchardEval_zero (x : Nat) :
    touchardEval 0 x = 1 := by
  unfold touchardEval touchardEvalPrefix touchardTerm touchardCoeff stirlingSecond
  exact Nat.mul_one 1

theorem touchardEvalPrefix_succ (n x k : Nat) :
    touchardEvalPrefix n x (Nat.succ k) =
      touchardEvalPrefix n x k + touchardTerm n x (Nat.succ k) := by
  rfl

theorem touchardEvalPrefix_one_eq_bellPrefix (n : Nat) :
    ∀ k : Nat,
      touchardEvalPrefix n 1 k = BEDC.Derived.BellNumberUp.bellStirlingPrefix n k
  | 0 => by
      unfold touchardEvalPrefix touchardTerm touchardCoeff stirlingSecond
      unfold BEDC.Derived.BellNumberUp.bellStirlingPrefix
      rw [natPow_one 0]
      exact Nat.mul_one (BEDC.Derived.StirlingUp.stirlingSecond n 0)
  | Nat.succ k => by
      change
        touchardEvalPrefix n 1 k +
            stirlingSecond n (Nat.succ k) * natPow 1 (Nat.succ k) =
          BEDC.Derived.BellNumberUp.bellStirlingPrefix n k +
            BEDC.Derived.StirlingUp.stirlingSecond n (Nat.succ k)
      rw [touchardEvalPrefix_one_eq_bellPrefix n k]
      rw [natPow_one (Nat.succ k)]
      exact congrArg
        (fun t => BEDC.Derived.BellNumberUp.bellStirlingPrefix n k + t)
        (Nat.mul_one (stirlingSecond n (Nat.succ k)))

theorem touchardEval_one_bellNumber (n : Nat) :
    touchardEval n 1 = bellNumber n := by
  unfold touchardEval bellNumber BEDC.Derived.BellNumberUp.bellNumber
  exact touchardEvalPrefix_one_eq_bellPrefix n n

theorem touchardEval_one_matches_StirlingBell (n : Nat) :
    touchardEval n 1 = BEDC.Derived.StirlingUp.bellNumber n := by
  rw [touchardEval_one_bellNumber n]
  exact BEDC.Derived.BellNumberUp.bellNumber_matches_StirlingUp n

theorem touchardStirlingStepPrefix_zero (n x : Nat) :
    touchardStirlingStepPrefix n x 0 =
      ((1 * stirlingSecond n 1) + stirlingSecond n 0) * natPow x 0 := by
  rfl

theorem touchardStirlingStepPrefix_succ (n x k : Nat) :
    touchardStirlingStepPrefix n x (Nat.succ k) =
      touchardStirlingStepPrefix n x k +
        ((Nat.succ (Nat.succ k) * stirlingSecond n (Nat.succ (Nat.succ k))) +
          stirlingSecond n (Nat.succ k)) * natPow x (Nat.succ k) := by
  rfl

private theorem nat_mul_assoc_clean (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun t => t + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := by
          rw [Nat.mul_succ b c]

private theorem nat_mul_pow_succ_shift (a x k : Nat) :
    a * natPow x (Nat.succ k) = x * (a * natPow x k) := by
  rw [natPow_succ]
  calc
    a * (x * natPow x k) = (a * x) * natPow x k :=
      (nat_mul_assoc_clean a x (natPow x k)).symm
    _ = (x * a) * natPow x k := by
      rw [Nat.mul_comm a x]
    _ = x * (a * natPow x k) := nat_mul_assoc_clean x a (natPow x k)

theorem stirlingSecond_succ_coeff_recurrence (n k : Nat) :
    touchardCoeff (Nat.succ n) (Nat.succ k) =
      Nat.succ k * touchardCoeff n (Nat.succ k) + touchardCoeff n k := by
  rfl

theorem touchardEvalPrefix_succ_stirling_step (n x : Nat) :
    ∀ k : Nat,
      touchardEvalPrefix (Nat.succ n) x (Nat.succ k) =
        x * touchardStirlingStepPrefix n x k
  | 0 => by
      change
        touchardEvalPrefix (Nat.succ n) x 0 + touchardTerm (Nat.succ n) x 1 =
          x * (((1 * stirlingSecond n 1) + stirlingSecond n 0) * natPow x 0)
      unfold touchardEvalPrefix touchardTerm touchardCoeff
      unfold stirlingSecond
      rw [BEDC.Derived.StirlingUp.stirlingSecond_succ_zero]
      rw [Nat.zero_mul, Nat.zero_add]
      rw [BEDC.Derived.StirlingUp.stirlingSecond_recurrence n 0]
      rw [natPow_zero_right]
      rw [natPow_succ, natPow_zero_right]
      rw [Nat.mul_one]
      rw [Nat.mul_one]
      exact Nat.mul_comm
        (Nat.succ 0 * BEDC.Derived.StirlingUp.stirlingSecond n (Nat.succ 0) +
          BEDC.Derived.StirlingUp.stirlingSecond n 0) x
  | Nat.succ k => by
      change
        touchardEvalPrefix (Nat.succ n) x (Nat.succ k) +
            touchardCoeff (Nat.succ n) (Nat.succ (Nat.succ k)) *
              natPow x (Nat.succ (Nat.succ k)) =
          x *
            (touchardStirlingStepPrefix n x k +
              ((Nat.succ (Nat.succ k) * stirlingSecond n (Nat.succ (Nat.succ k))) +
                stirlingSecond n (Nat.succ k)) * natPow x (Nat.succ k))
      rw [touchardEvalPrefix_succ_stirling_step n x k]
      rw [stirlingSecond_succ_coeff_recurrence n (Nat.succ k)]
      rw [nat_mul_pow_succ_shift
        (Nat.succ (Nat.succ k) * touchardCoeff n (Nat.succ (Nat.succ k)) +
          touchardCoeff n (Nat.succ k)) x (Nat.succ k)]
      exact (Nat.mul_add x (touchardStirlingStepPrefix n x k)
        (((Nat.succ (Nat.succ k) * stirlingSecond n (Nat.succ (Nat.succ k))) +
          stirlingSecond n (Nat.succ k)) * natPow x (Nat.succ k))).symm

theorem touchardEval_succ_recurrence (n x : Nat) :
    touchardEval (Nat.succ n) x =
      x * touchardStirlingStepPrefix n x n := by
  unfold touchardEval
  exact touchardEvalPrefix_succ_stirling_step n x n

theorem touchardBinomialRecurrencePrefix_zero (n x : Nat) :
    touchardBinomialRecurrencePrefix n x 0 =
      binomial n 0 * touchardEval 0 x := by
  rfl

theorem touchardBinomialRecurrencePrefix_succ (n x k : Nat) :
    touchardBinomialRecurrencePrefix n x (Nat.succ k) =
      touchardBinomialRecurrencePrefix n x k +
        binomial n (Nat.succ k) * touchardEval (Nat.succ k) x := by
  rfl

theorem touchardBinomialRecurrencePrefix_one_bellPrefix (n : Nat) :
    ∀ k : Nat,
      touchardBinomialRecurrencePrefix n 1 k =
        BEDC.Derived.BellNumberUp.bellRecurrencePrefix bellNumber n k
  | 0 => by
      unfold touchardBinomialRecurrencePrefix
      unfold BEDC.Derived.BellNumberUp.bellRecurrencePrefix
      rw [touchardEval_one_bellNumber 0]
      rfl
  | Nat.succ k => by
      change
        touchardBinomialRecurrencePrefix n 1 k +
            binomial n (Nat.succ k) * touchardEval (Nat.succ k) 1 =
          BEDC.Derived.BellNumberUp.bellRecurrencePrefix bellNumber n k +
            BEDC.Derived.BellNumberUp.natChooseCount n (Nat.succ k) *
              bellNumber (Nat.succ k)
      rw [touchardBinomialRecurrencePrefix_one_bellPrefix n k]
      rw [touchardEval_one_bellNumber (Nat.succ k)]
      rfl

theorem touchardBell_binomial_recurrence_surface (n : Nat) :
    touchardBinomialRecurrencePrefix n 1 n =
      BEDC.Derived.BellNumberUp.bellRecurrencePrefix bellNumber n n := by
  exact touchardBinomialRecurrencePrefix_one_bellPrefix n n

theorem TouchardPolyUp_constructive_export :
    (∀ n : Nat, touchardEval n 1 = bellNumber n) ∧
      (∀ n x : Nat,
        touchardEval (Nat.succ n) x =
          x * touchardStirlingStepPrefix n x n) ∧
      (∀ n k : Nat,
        touchardCoeff (Nat.succ n) (Nat.succ k) =
          Nat.succ k * touchardCoeff n (Nat.succ k) + touchardCoeff n k) ∧
      (∀ n : Nat,
        touchardBinomialRecurrencePrefix n 1 n =
          BEDC.Derived.BellNumberUp.bellRecurrencePrefix bellNumber n n) := by
  constructor
  · intro n
    exact touchardEval_one_bellNumber n
  · constructor
    · intro n x
      exact touchardEval_succ_recurrence n x
    · constructor
      · intro n k
        exact stirlingSecond_succ_coeff_recurrence n k
      · intro n
        exact touchardBell_binomial_recurrence_surface n

end BEDC.Derived.TouchardPolyUp
