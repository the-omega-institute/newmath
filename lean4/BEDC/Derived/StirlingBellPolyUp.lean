import BEDC.Derived.BellNumberUp
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.TouchardPolyUp

namespace BEDC.Derived.StirlingBellPolyUp

abbrev stirlingSecond : Nat -> Nat -> Nat :=
  BEDC.Derived.StirlingUp.stirlingSecond

abbrev bellNumber : Nat -> Nat :=
  BEDC.Derived.BellNumberUp.bellNumber

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

abbrev finiteNatSum (f : Nat -> Nat) : Nat -> Nat :=
  BEDC.Derived.BinomialIdentitiesUp.finiteFoldNatSum f

abbrev touchardEval : Nat -> Nat -> Nat :=
  BEDC.Derived.TouchardPolyUp.touchardEval

-- `natPow x k` 是 fuel 型幂函数, 用于保持求和停留在 List/fuel 层。
def natPow (x : Nat) : Nat -> Nat
  | 0 => 1
  | Nat.succ k => x * natPow x k

def bellPolynomialTerm (n x k : Nat) : Nat :=
  stirlingSecond n k * natPow x k

def bellPolynomialStirlingSum (n x : Nat) : Nat :=
  finiteNatSum (bellPolynomialTerm n x) n

def bellPolynomial (n x : Nat) : Nat :=
  bellPolynomialStirlingSum n x

def touchardConvolutionPrefix (n x : Nat) : Nat -> Nat
  | 0 => C n 0 * bellPolynomial 0 x
  | Nat.succ k =>
      touchardConvolutionPrefix n x k +
        C n (Nat.succ k) * bellPolynomial (Nat.succ k) x

def touchardConvolution (n x : Nat) : Nat :=
  touchardConvolutionPrefix n x n

def touchardNext (n x : Nat) : Nat :=
  x * touchardConvolution n x

def touchardRecurrenceAt (n x : Nat) : Prop :=
  bellPolynomial (Nat.succ n) x = touchardNext n x

theorem natPow_zero (x : Nat) :
    natPow x 0 = 1 := by
  rfl

theorem natPow_succ (x k : Nat) :
    natPow x (Nat.succ k) = x * natPow x k := by
  rfl

theorem natPow_one :
    forall k : Nat, natPow 1 k = 1
  | 0 => rfl
  | Nat.succ k => by
      change 1 * natPow 1 k = 1
      rw [natPow_one k]

theorem natPow_matches_TouchardPolyUp (x : Nat) :
    forall k : Nat,
      natPow x k = BEDC.Derived.TouchardPolyUp.natPow x k
  | 0 => rfl
  | Nat.succ k => by
      change
        x * natPow x k =
          x * BEDC.Derived.TouchardPolyUp.natPow x k
      rw [natPow_matches_TouchardPolyUp x k]

theorem bellPolynomialTerm_one (n k : Nat) :
    bellPolynomialTerm n 1 k = stirlingSecond n k := by
  unfold bellPolynomialTerm
  rw [natPow_one k]
  exact Nat.mul_one (stirlingSecond n k)

theorem bellPolynomial_stirling_sum (n x : Nat) :
    bellPolynomial n x =
      finiteNatSum (fun k => stirlingSecond n k * natPow x k) n := by
  rfl

theorem bellPolynomialStirlingSum_matches_touchardEvalPrefix (n x : Nat) :
    forall k : Nat,
      finiteNatSum (bellPolynomialTerm n x) k =
        BEDC.Derived.TouchardPolyUp.touchardEvalPrefix n x k
  | 0 => by
      unfold bellPolynomialTerm
      unfold BEDC.Derived.TouchardPolyUp.touchardEvalPrefix
      unfold BEDC.Derived.TouchardPolyUp.touchardTerm
      unfold BEDC.Derived.TouchardPolyUp.touchardCoeff
      change
        stirlingSecond n 0 * natPow x 0 =
          BEDC.Derived.TouchardPolyUp.stirlingSecond n 0 *
            BEDC.Derived.TouchardPolyUp.natPow x 0
      rw [natPow_matches_TouchardPolyUp x 0]
  | Nat.succ k => by
      change finiteNatSum (bellPolynomialTerm n x) k +
          bellPolynomialTerm n x (Nat.succ k) =
        BEDC.Derived.TouchardPolyUp.touchardEvalPrefix n x k +
          BEDC.Derived.TouchardPolyUp.touchardTerm n x (Nat.succ k)
      rw [bellPolynomialStirlingSum_matches_touchardEvalPrefix n x k]
      unfold bellPolynomialTerm
      unfold BEDC.Derived.TouchardPolyUp.touchardTerm
      unfold BEDC.Derived.TouchardPolyUp.touchardCoeff
      rw [natPow_matches_TouchardPolyUp x (Nat.succ k)]

theorem bellPolynomial_eq_touchardEval (n x : Nat) :
    bellPolynomial n x = touchardEval n x := by
  unfold bellPolynomial bellPolynomialStirlingSum touchardEval
  exact bellPolynomialStirlingSum_matches_touchardEvalPrefix n x n

theorem bellPolynomialStirlingSum_one_prefix (n : Nat) :
    forall k : Nat,
      finiteNatSum (bellPolynomialTerm n 1) k =
        BEDC.Derived.BellNumberUp.bellStirlingPrefix n k
  | 0 => by
      change stirlingSecond n 0 * natPow 1 0 = stirlingSecond n 0
      exact Nat.mul_one (stirlingSecond n 0)
  | Nat.succ k => by
      change finiteNatSum (bellPolynomialTerm n 1) k +
          bellPolynomialTerm n 1 (Nat.succ k) =
        BEDC.Derived.BellNumberUp.bellStirlingPrefix n k +
          stirlingSecond n (Nat.succ k)
      rw [bellPolynomialStirlingSum_one_prefix n k]
      rw [bellPolynomialTerm_one n (Nat.succ k)]

theorem bellPolynomial_one_eq_bellNumber (n : Nat) :
    bellPolynomial n 1 = bellNumber n := by
  unfold bellPolynomial bellPolynomialStirlingSum bellNumber
  rw [bellPolynomialStirlingSum_one_prefix n n]
  rfl

theorem bellPolynomial_one_eq_StirlingUp_bellNumber (n : Nat) :
    bellPolynomial n 1 = BEDC.Derived.StirlingUp.bellNumber n := by
  rw [bellPolynomial_one_eq_bellNumber n]
  exact BEDC.Derived.BellNumberUp.bellNumber_matches_StirlingUp n

theorem bellPolynomial_zero (x : Nat) :
    bellPolynomial 0 x = 1 := by
  rfl

theorem bellPolynomial_one_degree (x : Nat) :
    bellPolynomial 1 x = x := by
  change 0 * 1 + 1 * (x * 1) = x
  rw [Nat.zero_mul, Nat.zero_add, Nat.one_mul, Nat.mul_one]

theorem bellPolynomial_two_degree (x : Nat) :
    bellPolynomial 2 x = x + x * x := by
  change
    (0 * 1 + 1 * (x * 1)) + 1 * (x * (x * 1)) = x + x * x
  rw [Nat.zero_mul, Nat.zero_add, Nat.one_mul, Nat.mul_one]
  rw [Nat.one_mul]

theorem touchardConvolution_zero (n x : Nat) :
    touchardConvolutionPrefix n x 0 = C n 0 * bellPolynomial 0 x := by
  rfl

theorem touchardConvolution_succ (n x k : Nat) :
    touchardConvolutionPrefix n x (Nat.succ k) =
      touchardConvolutionPrefix n x k +
        C n (Nat.succ k) * bellPolynomial (Nat.succ k) x := by
  rfl

theorem touchardNext_definition (n x : Nat) :
    touchardNext n x = x * touchardConvolutionPrefix n x n := by
  rfl

theorem touchardRecurrenceAt_zero (x : Nat) :
    touchardRecurrenceAt 0 x := by
  unfold touchardRecurrenceAt touchardNext touchardConvolution
  rw [bellPolynomial_one_degree x]
  change x = x * (C 0 0 * bellPolynomial 0 x)
  rw [bellPolynomial_zero x]
  change x = x * (1 * 1)
  rw [Nat.one_mul]
  exact (Nat.mul_one x).symm

theorem touchardRecurrenceAt_one (x : Nat) :
    touchardRecurrenceAt 1 x := by
  unfold touchardRecurrenceAt touchardNext touchardConvolution
  rw [bellPolynomial_two_degree x]
  change x + x * x =
    x * (C 1 0 * bellPolynomial 0 x + C 1 1 * bellPolynomial 1 x)
  rw [bellPolynomial_zero x]
  rw [bellPolynomial_one_degree x]
  change x + x * x = x * (1 * 1 + 1 * x)
  rw [Nat.one_mul]
  rw [Nat.one_mul]
  rw [Nat.mul_add]
  rw [Nat.mul_one]

theorem StirlingBellPolyUp_constructive_export :
    (forall n x : Nat,
      bellPolynomial n x =
        finiteNatSum (fun k => stirlingSecond n k * natPow x k) n) /\
      (forall n x : Nat, bellPolynomial n x = touchardEval n x) /\
        (forall n : Nat, bellPolynomial n 1 = bellNumber n) /\
          (forall x : Nat, touchardRecurrenceAt 0 x) /\
            (forall x : Nat, touchardRecurrenceAt 1 x) := by
  constructor
  · intro n x
    exact bellPolynomial_stirling_sum n x
  · constructor
    · intro n x
      exact bellPolynomial_eq_touchardEval n x
    · constructor
      · intro n
        exact bellPolynomial_one_eq_bellNumber n
      · constructor
        · intro x
          exact touchardRecurrenceAt_zero x
        · intro x
          exact touchardRecurrenceAt_one x

end BEDC.Derived.StirlingBellPolyUp
