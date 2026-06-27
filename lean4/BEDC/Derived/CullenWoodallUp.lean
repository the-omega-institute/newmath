import BEDC.Derived.NatUp.NatAdd
import BEDC.Derived.PrimeUp.NatMulComm
import BEDC.Derived.PrimeUp.NatMulTransport
import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.IntUp.CommRing

namespace BEDC.Derived.CullenWoodallUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Mark (BMark)
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)
open BEDC.Derived.RationalUp

-- 二的幂用闭递归给出, 不借助外部搜索或商结构。
def twoPow : Nat -> Nat
  | 0 => 1
  | Nat.succ n => 2 * twoPow n

def predNat : Nat -> Nat
  | 0 => 0
  | Nat.succ n => n

def cullenCoreNat (n : Nat) : Nat :=
  n * twoPow n

def cullenNat (n : Nat) : Nat :=
  cullenCoreNat n + 1

def woodallNat (n : Nat) : Nat :=
  predNat (cullenCoreNat n)

def cullenCore (n : Nat) : BHist :=
  natToUnary (cullenCoreNat n)

def cullen (n : Nat) : BHist :=
  natToUnary (cullenNat n)

def woodall (n : Nat) : BHist :=
  natToUnary (woodallNat n)

def cullenCoreInt (n : Nat) : IntegerUp :=
  intOfNat (cullenCore n) (by
    unfold cullenCore
    exact natToUnary_unary _)

def cullenInt (n : Nat) : IntegerUp :=
  IntAdd (cullenCoreInt n) intOne

def woodallInt (n : Nat) : IntegerUp :=
  IntAdd (cullenCoreInt n) (IntNeg intOne)

private theorem natToUnary_append (m n : Nat) :
    append (natToUnary m) (natToUnary n) = natToUnary (m + n) := by
  induction n with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ n ih =>
      change BHist.e1 (append (natToUnary m) (natToUnary n)) =
        natToUnary (m + Nat.succ n)
      rw [ih]
      rw [Nat.add_succ]
      rfl

private theorem unary_hsame_of_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k -> hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr lengthEq

private theorem natToUnary_mul_rel (a b : Nat) :
    NatMul (natToUnary a) (natToUnary b) (natToUnary (a * b)) := by
  have total := NatMul_total (natToUnary_unary a) (natToUnary_unary b)
  cases total with
  | intro result resultData =>
      have sameResult : hsame result (natToUnary (a * b)) :=
        unary_hsame_of_length resultData.left (natToUnary_unary _)
          ((NatMul_bwordLength resultData.right).trans (by
            rw [natToUnary_length, natToUnary_length, natToUnary_length]))
      exact (NatMul_result_hsame_transport resultData.right sameResult).right

theorem twoPow_zero :
    twoPow 0 = 1 := by
  rfl

theorem twoPow_succ (n : Nat) :
    twoPow (Nat.succ n) = 2 * twoPow n := by
  rfl

theorem twoPow_pos (n : Nat) :
    0 < twoPow n := by
  induction n with
  | zero =>
      exact Nat.succ_pos 0
  | succ n ih =>
      change 0 < 2 * twoPow n
      exact Nat.mul_pos (Nat.succ_pos 1) ih

theorem cullenNat_definition (n : Nat) :
    cullenNat n = n * twoPow n + 1 := by
  rfl

theorem woodallNat_definition (n : Nat) :
    woodallNat n = n * twoPow n - 1 := by
  unfold woodallNat cullenCoreNat
  cases n * twoPow n with
  | zero =>
      rfl
  | succ k =>
      rfl

theorem cullenNat_succ_formula (n : Nat) :
    cullenNat (Nat.succ n) =
      Nat.succ n * (2 * twoPow n) + 1 := by
  unfold cullenNat cullenCoreNat
  rw [twoPow_succ]

theorem woodallNat_succ_formula (n : Nat) :
    woodallNat (Nat.succ n) =
      Nat.succ n * (2 * twoPow n) - 1 := by
  rw [woodallNat_definition, twoPow_succ]

theorem cullenCore_unary (n : Nat) :
    UnaryHistory (cullenCore n) := by
  unfold cullenCore
  exact natToUnary_unary _

theorem cullen_unary (n : Nat) :
    UnaryHistory (cullen n) := by
  unfold cullen
  exact natToUnary_unary _

theorem woodall_unary (n : Nat) :
    UnaryHistory (woodall n) := by
  unfold woodall
  exact natToUnary_unary _

theorem cullenCoreInt_pair (n : Nat) :
    intToPair (cullenCoreInt n) = (cullenCore n, BHist.Empty) := by
  unfold cullenCoreInt intOfNat intToPair
  rfl

theorem cullenInt_definition (n : Nat) :
    cullenInt n = IntAdd (cullenCoreInt n) intOne := by
  rfl

theorem woodallInt_definition (n : Nat) :
    woodallInt n = IntAdd (cullenCoreInt n) (IntNeg intOne) := by
  rfl

theorem cullenCore_mul_rel (n : Nat) :
    NatMul (natToUnary n) (natToUnary (twoPow n)) (cullenCore n) := by
  unfold cullenCore cullenCoreNat
  exact natToUnary_mul_rel n (twoPow n)

theorem cullenCore_divisible_by_index (n : Nat) :
    NatDivides (natToUnary n) (cullenCore n) := by
  exact ⟨natToUnary (twoPow n), natToUnary_unary _, cullenCore_mul_rel n⟩

theorem cullenNat_minus_one (n : Nat) :
    cullenNat n - 1 = cullenCoreNat n := by
  unfold cullenNat
  cases cullenCoreNat n with
  | zero => rfl
  | succ k => rfl

theorem cullenNat_minus_one_divisible_by_index (n : Nat) :
    NatDivides (natToUnary n) (natToUnary (cullenNat n - 1)) := by
  have dividesCore := cullenCore_divisible_by_index n
  have sameTarget :
      hsame (cullenCore n) (natToUnary (cullenNat n - 1)) := by
    apply unary_hsame_of_length
    · exact cullenCore_unary n
    · exact natToUnary_unary _
    · rw [cullenCore, natToUnary_length, natToUnary_length, cullenNat_minus_one]
  exact (NatDivides_dividend_hsame_transport dividesCore sameTarget).right

theorem cullenNat_add_one_rel (n : Nat) :
    NatAdd (cullenCore n) (natToUnary 1) (cullen n) := by
  constructor
  · exact cullenCore_unary n
  · constructor
    · exact natToUnary_unary 1
    · unfold cullenCore cullen cullenNat
      exact cont_intro (natToUnary_append (cullenCoreNat n) 1).symm

theorem cullenCoreNat_succ_pos (n : Nat) :
    0 < cullenCoreNat (Nat.succ n) := by
  unfold cullenCoreNat
  exact Nat.mul_pos (Nat.succ_pos n) (twoPow_pos (Nat.succ n))

theorem woodallNat_succ_plus_one (n : Nat) :
    woodallNat (Nat.succ n) + 1 = cullenCoreNat (Nat.succ n) := by
  unfold woodallNat
  cases coreEq : cullenCoreNat (Nat.succ n) with
  | zero =>
      have corePos := cullenCoreNat_succ_pos n
      rw [coreEq] at corePos
      cases corePos
  | succ k =>
      rfl

theorem woodallNat_succ_plus_one_divisible_by_index (n : Nat) :
    NatDivides (natToUnary (Nat.succ n))
      (natToUnary (woodallNat (Nat.succ n) + 1)) := by
  have dividesCore := cullenCore_divisible_by_index (Nat.succ n)
  have sameTarget :
      hsame (cullenCore (Nat.succ n))
        (natToUnary (woodallNat (Nat.succ n) + 1)) := by
    apply unary_hsame_of_length
    · exact cullenCore_unary (Nat.succ n)
    · exact natToUnary_unary _
    · rw [cullenCore, natToUnary_length, natToUnary_length,
        woodallNat_succ_plus_one]
  exact (NatDivides_dividend_hsame_transport dividesCore sameTarget).right

theorem woodallNat_add_one_rel_succ (n : Nat) :
    NatAdd (woodall (Nat.succ n)) (natToUnary 1) (cullenCore (Nat.succ n)) := by
  constructor
  · exact woodall_unary (Nat.succ n)
  · constructor
    · exact natToUnary_unary 1
    · unfold woodall cullenCore
      apply cont_intro
      apply unary_hsame_of_length
      · exact natToUnary_unary _
      · exact unary_append_closed (natToUnary_unary _) (natToUnary_unary 1)
      · rw [BEDC.FKernel.ExternalBinary.bwordLength_append]
        rw [natToUnary_length, natToUnary_length, natToUnary_length,
          woodallNat_succ_plus_one]

theorem cullenNat_zero :
    cullenNat 0 = 1 := by
  rfl

theorem cullenNat_one :
    cullenNat 1 = 3 := by
  rfl

theorem cullenNat_two :
    cullenNat 2 = 9 := by
  rfl

theorem cullenNat_three :
    cullenNat 3 = 25 := by
  rfl

theorem cullenNat_four :
    cullenNat 4 = 65 := by
  rfl

theorem woodallNat_zero :
    woodallNat 0 = 0 := by
  rfl

theorem woodallNat_one :
    woodallNat 1 = 1 := by
  rfl

theorem woodallNat_two :
    woodallNat 2 = 7 := by
  rfl

theorem woodallNat_three :
    woodallNat 3 = 23 := by
  rfl

theorem woodallNat_four :
    woodallNat 4 = 63 := by
  rfl

theorem cullen_zero_hist :
    cullen 0 = natToUnary 1 := by
  rfl

theorem cullen_one_hist :
    cullen 1 = natToUnary 3 := by
  rfl

theorem woodall_zero_hist :
    woodall 0 = natToUnary 0 := by
  rfl

theorem woodall_two_hist :
    woodall 2 = natToUnary 7 := by
  rfl

theorem cullenInt_zero :
    IntEq (cullenInt 0) intOne := by
  change IntEq (IntAdd intZero intOne) intOne
  exact IntAdd_zero_left _

theorem cullenInt_one :
    IntEq (cullenInt 1) (intOfNat (natToUnary 3) (natToUnary_unary 3)) := by
  unfold cullenInt cullenCoreInt cullenCore cullenCoreNat twoPow intOne
    intOfNat IntAdd
  exact IntEq_refl _

theorem cullenInt_two :
    IntEq (cullenInt 2) (intOfNat (natToUnary 9) (natToUnary_unary 9)) := by
  unfold cullenInt cullenCoreInt cullenCore cullenCoreNat twoPow intOne
    intOfNat IntAdd
  exact IntEq_refl _

theorem cullenInt_four :
    IntEq (cullenInt 4) (intOfNat (natToUnary 65) (natToUnary_unary 65)) := by
  unfold cullenInt cullenCoreInt cullenCore cullenCoreNat twoPow intOne
    intOfNat IntAdd
  exact IntEq_refl _

theorem woodallInt_zero :
    IntEq (woodallInt 0)
      (intOfNatWithSign BMark.b1 (natToUnary 1) (natToUnary_unary 1)) := by
  unfold woodallInt cullenCoreInt cullenCore cullenCoreNat twoPow intOne
    intOfNat IntAdd IntNeg intOfNatWithSign
  exact IntEq_refl _

theorem woodallInt_one :
    IntEq (woodallInt 1) intOne := by
  unfold woodallInt cullenCoreInt cullenCore cullenCoreNat twoPow intOne
    intOfNat IntAdd IntNeg
  exact IntEq_refl _

theorem woodallInt_two :
    IntEq (woodallInt 2) (intOfNat (natToUnary 7) (natToUnary_unary 7)) := by
  unfold woodallInt cullenCoreInt cullenCore cullenCoreNat twoPow intOne
    intOfNat IntAdd IntNeg
  exact IntEq_refl _

theorem woodallInt_four :
    IntEq (woodallInt 4) (intOfNat (natToUnary 63) (natToUnary_unary 63)) := by
  unfold woodallInt cullenCoreInt cullenCore cullenCoreNat twoPow intOne
    intOfNat IntAdd IntNeg
  exact IntEq_refl _

end BEDC.Derived.CullenWoodallUp
