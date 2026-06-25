import BEDC.Derived.NatUp.NatAdd
import BEDC.Derived.PrimeUp.NatMulComm
import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.IntUp.CommRing
import BEDC.Derived.FactorialUp

namespace BEDC.Derived.StirlingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.NatUp
open BEDC.Derived.FactorialUp
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

abbrev UnaryOne : BHist := BHist.e1 BHist.Empty
abbrev UnaryTwo : BHist := BHist.e1 UnaryOne

-- 第二类 Stirling 数的闭递归定义。
def stirlingSecond : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 0
  | Nat.succ n, Nat.succ k =>
      Nat.succ k * stirlingSecond n (Nat.succ k) + stirlingSecond n k

def bellPrefix (n : Nat) : Nat -> Nat
  | 0 => stirlingSecond n 0
  | Nat.succ k => bellPrefix n k + stirlingSecond n (Nat.succ k)

def bellNumber (n : Nat) : Nat :=
  bellPrefix n n

def stirlingSecondFn (n k : BHist) : BHist :=
  natToUnary (stirlingSecond (bwordLength n) (bwordLength k))

def bellNumberFn (n : BHist) : BHist :=
  natToUnary (bellNumber (bwordLength n))

def chooseTwo : Nat -> Nat
  | 0 => 0
  | Nat.succ n => n + chooseTwo n

theorem natToUnary_append (m n : Nat) :
    BEDC.FKernel.Cont.append (natToUnary m) (natToUnary n) = natToUnary (m + n) := by
  induction n with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ n ih =>
      change BHist.e1 (BEDC.FKernel.Cont.append (natToUnary m) (natToUnary n)) =
        natToUnary (m + Nat.succ n)
      rw [ih]
      rw [Nat.add_succ]
      rfl

theorem natToUnary_add_rel (m n : Nat) :
    NatAdd (natToUnary m) (natToUnary n) (natToUnary (m + n)) := by
  exact
    ⟨natToUnary_unary m, natToUnary_unary n,
      cont_intro (natToUnary_append m n).symm⟩

theorem natToUnary_one_left_cont (n : Nat) :
    Cont UnaryOne (natToUnary n) (natToUnary (Nat.succ n)) := by
  induction n with
  | zero =>
      rfl
  | succ _ ih =>
      change BHist.e1 (natToUnary _) =
        BHist.e1 (BEDC.FKernel.Cont.append UnaryOne _)
      exact congrArg BHist.e1 ih

theorem natToUnary_one_left_add (n : Nat) :
    NatAdd UnaryOne (natToUnary n) (natToUnary (Nat.succ n)) := by
  exact
    ⟨unary_e1_closed unary_empty, natToUnary_unary n,
      natToUnary_one_left_cont n⟩

theorem natToUnary_two_left_cont (n : Nat) :
    Cont UnaryTwo (natToUnary n) (natToUnary (Nat.succ (Nat.succ n))) := by
  induction n with
  | zero =>
      rfl
  | succ _ ih =>
      change BHist.e1 (natToUnary _) =
        BHist.e1 (BEDC.FKernel.Cont.append UnaryTwo _)
      exact congrArg BHist.e1 ih

theorem stirlingSecond_zero_zero :
    stirlingSecond 0 0 = 1 := by
  rfl

theorem stirlingSecond_zero_succ (k : Nat) :
    stirlingSecond 0 (Nat.succ k) = 0 := by
  rfl

theorem stirlingSecond_succ_zero (n : Nat) :
    stirlingSecond (Nat.succ n) 0 = 0 := by
  rfl

theorem stirlingSecond_zero_boundary (n : Nat) :
    stirlingSecond n 0 = if n = 0 then 1 else 0 := by
  cases n with
  | zero =>
      rfl
  | succ _ =>
      rfl

theorem stirlingSecond_recurrence (n k : Nat) :
    stirlingSecond (Nat.succ n) (Nat.succ k) =
      Nat.succ k * stirlingSecond n (Nat.succ k) + stirlingSecond n k := by
  rfl

theorem stirlingSecond_self_and_above :
    ∀ n : Nat, stirlingSecond n n = 1 ∧
      ∀ extra : Nat, stirlingSecond n (Nat.succ (n + extra)) = 0 := by
  intro n
  induction n with
  | zero =>
      constructor
      · rfl
      · intro extra
        rfl
  | succ n ih =>
      constructor
      · change Nat.succ n * stirlingSecond n (Nat.succ n) +
          stirlingSecond n n = 1
        rw [ih.right 0, ih.left]
        rfl
      · intro extra
        change
          Nat.succ (Nat.succ n + extra) *
              stirlingSecond n (Nat.succ (Nat.succ n + extra)) +
            stirlingSecond n (Nat.succ n + extra) = 0
        rw [Nat.succ_add]
        rw [ih.right extra]
        rw [show Nat.succ (Nat.succ (n + extra)) =
            Nat.succ (n + Nat.succ extra) by
          rw [Nat.add_succ]]
        rw [ih.right (Nat.succ extra)]
        rfl

theorem stirlingSecond_self (n : Nat) :
    stirlingSecond n n = 1 :=
  (stirlingSecond_self_and_above n).left

theorem stirlingSecond_above (n extra : Nat) :
    stirlingSecond n (Nat.succ (n + extra)) = 0 :=
  (stirlingSecond_self_and_above n).right extra

theorem stirlingSecond_succ_one :
    ∀ n : Nat, stirlingSecond (Nat.succ n) 1 = 1 := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change 1 * stirlingSecond (Nat.succ n) 1 +
        stirlingSecond (Nat.succ n) 0 = 1
      rw [ih]
      rfl

theorem stirlingSecond_succ_pred_chooseTwo :
    ∀ n : Nat, stirlingSecond (Nat.succ n) n = chooseTwo (Nat.succ n) := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change Nat.succ n * stirlingSecond (Nat.succ n) (Nat.succ n) +
        stirlingSecond (Nat.succ n) n =
          Nat.succ n + chooseTwo (Nat.succ n)
      rw [stirlingSecond_self (Nat.succ n), ih]
      rw [Nat.mul_one]

theorem stirlingSecond_near_diagonal_chooseTwo (n : Nat) :
    stirlingSecond (Nat.succ (Nat.succ n)) (Nat.succ n) =
      chooseTwo (Nat.succ (Nat.succ n)) :=
  stirlingSecond_succ_pred_chooseTwo (Nat.succ n)

theorem NatBinom_one_natToUnary (n : Nat) :
    NatBinom UnaryOne (natToUnary n) (natToUnary (Nat.succ n)) := by
  induction n with
  | zero =>
      change NatBinom UnaryOne BHist.Empty UnaryOne
      exact NatBinom.right (unary_e1_closed unary_empty)
  | succ n ih =>
      change NatBinom UnaryOne (BHist.e1 (natToUnary n))
        (natToUnary (Nat.succ (Nat.succ n)))
      exact NatBinom.step
        (NatBinom.left (unary_e1_closed (natToUnary_unary n)))
        ih
        (natToUnary_one_left_add (Nat.succ n))

theorem NatBinom_two_natToUnary (n : Nat) :
    NatBinom UnaryTwo (natToUnary n)
      (natToUnary (chooseTwo (Nat.succ (Nat.succ n)))) := by
  induction n with
  | zero =>
      change NatBinom UnaryTwo BHist.Empty UnaryOne
      exact NatBinom.right (unary_e1_closed (unary_e1_closed unary_empty))
  | succ n ih =>
      change NatBinom UnaryTwo (BHist.e1 (natToUnary n))
        (natToUnary (chooseTwo (Nat.succ (Nat.succ (Nat.succ n)))))
      exact NatBinom.step
        (NatBinom_one_natToUnary (Nat.succ n))
        ih
        (natToUnary_add_rel (Nat.succ (Nat.succ n))
          (chooseTwo (Nat.succ (Nat.succ n))))

theorem NatChoose_two_natToUnary (n : Nat) :
    NatChoose (natToUnary (Nat.succ (Nat.succ n))) UnaryTwo
      (natToUnary (chooseTwo (Nat.succ (Nat.succ n)))) := by
  exact
    ⟨natToUnary n,
      ⟨unary_e1_closed (unary_e1_closed unary_empty), natToUnary_unary n,
        natToUnary_two_left_cont n⟩,
      NatBinom_two_natToUnary n⟩

theorem stirlingSecondFn_unary_result (n k : BHist) :
    UnaryHistory (stirlingSecondFn n k) := by
  unfold stirlingSecondFn
  exact natToUnary_unary _

theorem bellNumberFn_unary_result (n : BHist) :
    UnaryHistory (bellNumberFn n) := by
  unfold bellNumberFn
  exact natToUnary_unary _

theorem stirlingSecondFn_recurrence_natToUnary (n k : Nat) :
    stirlingSecondFn (natToUnary (Nat.succ n)) (natToUnary (Nat.succ k)) =
      natToUnary
        (Nat.succ k * stirlingSecond n (Nat.succ k) + stirlingSecond n k) := by
  unfold stirlingSecondFn
  rw [natToUnary_length, natToUnary_length]
  rfl

theorem stirlingSecondFn_zero_boundary (n : Nat) :
    stirlingSecondFn (natToUnary n) BHist.Empty =
      if n = 0 then UnaryOne else BHist.Empty := by
  unfold stirlingSecondFn
  rw [natToUnary_length]
  cases n with
  | zero =>
      rfl
  | succ _ =>
      rfl

theorem stirlingSecondFn_self (n : Nat) :
    stirlingSecondFn (natToUnary n) (natToUnary n) = UnaryOne := by
  unfold stirlingSecondFn
  rw [natToUnary_length]
  rw [stirlingSecond_self]
  rfl

theorem stirlingSecondFn_succ_one (n : Nat) :
    stirlingSecondFn (natToUnary (Nat.succ n)) UnaryOne = UnaryOne := by
  unfold stirlingSecondFn
  rw [natToUnary_length]
  change natToUnary (stirlingSecond (Nat.succ n) 1) = UnaryOne
  rw [stirlingSecond_succ_one]
  rfl

theorem stirlingSecondFn_near_diagonal_NatChoose (n : Nat) :
    NatChoose (natToUnary (Nat.succ (Nat.succ n))) UnaryTwo
      (stirlingSecondFn (natToUnary (Nat.succ (Nat.succ n)))
        (natToUnary (Nat.succ n))) := by
  unfold stirlingSecondFn
  rw [natToUnary_length, natToUnary_length, stirlingSecond_near_diagonal_chooseTwo]
  exact NatChoose_two_natToUnary n

theorem bellPrefix_succ (n k : Nat) :
    bellPrefix n (Nat.succ k) =
      bellPrefix n k + stirlingSecond n (Nat.succ k) := by
  rfl

theorem bellNumber_definition (n : Nat) :
    bellNumber n = bellPrefix n n := by
  rfl

theorem bellNumber_zero :
    bellNumber 0 = 1 := by
  rfl

theorem bellNumberFn_zero :
    bellNumberFn BHist.Empty = UnaryOne := by
  rfl

end BEDC.Derived.StirlingUp
