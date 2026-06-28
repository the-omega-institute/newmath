import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.PadicUp.IntegerTower
import BEDC.Derived.PrimeUp.UniqueFactorization
import BEDC.Derived.ZModUp

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

namespace BEDC.Derived.LucasLehmerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.NatUp
open BEDC.Derived.IntUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModUp

abbrev NatTwo : BHist := natToUnary 2
abbrev NatThree : BHist := natToUnary 3
abbrev NatFive : BHist := natToUnary 5
abbrev NatSeven : BHist := natToUnary 7
abbrev MersenneThree : BHist := natToUnary 7
abbrev MersenneFive : BHist := natToUnary 31
abbrev MersenneSeven : BHist := natToUnary 127

def mersenneNat (p : Nat) : Nat :=
  2 ^ p - 1

abbrev mersenne (p : Nat) : BHist :=
  natToUnary (mersenneNat p)

def lucasLehmerTerm : Nat -> Nat
  | 0 => 4
  | n + 1 => lucasLehmerTerm n * lucasLehmerTerm n - 2

def lucasLehmerStepMod (M r : BHist) : BHist :=
  natModFn M (append (natMulFn r r) (natComplementMod M NatTwo))

def lucasLehmerResidueFuel (M : BHist) : Nat -> BHist
  | 0 => natModFn M (natToUnary 4)
  | n + 1 => lucasLehmerStepMod M (lucasLehmerResidueFuel M n)

abbrev lucasLehmerResidue (p : Nat) : BHist :=
  lucasLehmerResidueFuel (mersenne p) (p - 2)

def lucasLehmerStepModNat (M r : Nat) : Nat :=
  (r * r + (M - 2)) % M

def lucasLehmerResidueFuelNat (M : Nat) : Nat -> Nat
  | 0 => 4 % M
  | n + 1 => lucasLehmerStepModNat M (lucasLehmerResidueFuelNat M n)

def lucasLehmerResidueNat (p : Nat) : Nat :=
  lucasLehmerResidueFuelNat (mersenneNat p) (p - 2)

def LucasLehmerCriterionBoundary (p : Nat) : Prop :=
  NatPrime (mersenne p) ↔ hsame (lucasLehmerResidue p) BHist.Empty

def LucasLehmerDividesTerm (p : Nat) : Prop :=
  NatDivides (mersenne p) (natToUnary (lucasLehmerTerm (p - 2)))

def LucasLehmerDivisibilityCriterion (p : Nat) : Prop :=
  NatPrime (mersenne p) ↔ LucasLehmerDividesTerm p

structure LucasLehmerCriterionData (p : Nat) where
  prime_iff_divides : LucasLehmerDivisibilityCriterion p
  prime_iff_zero : LucasLehmerCriterionBoundary p

theorem lucasLehmerCriterionData_prime_iff_divides
    {p : Nat} (data : LucasLehmerCriterionData p) :
    NatPrime (mersenne p) ↔ LucasLehmerDividesTerm p :=
  data.prime_iff_divides

theorem lucasLehmerCriterionData_prime_iff_zero
    {p : Nat} (data : LucasLehmerCriterionData p) :
    NatPrime (mersenne p) ↔ hsame (lucasLehmerResidue p) BHist.Empty :=
  data.prime_iff_zero

theorem mersenne_three_value :
    mersenneNat 3 = 7 := by
  rfl

theorem mersenne_five_value :
    mersenneNat 5 = 31 := by
  rfl

theorem mersenne_seven_value :
    mersenneNat 7 = 127 := by
  rfl

theorem mersenne_three_hist :
    mersenne 3 = MersenneThree := by
  rfl

theorem mersenne_five_hist :
    mersenne 5 = MersenneFive := by
  rfl

theorem mersenne_seven_hist :
    mersenne 7 = MersenneSeven := by
  rfl

theorem lucasLehmerTerm_zero :
    lucasLehmerTerm 0 = 4 := by
  rfl

theorem lucasLehmerTerm_succ (n : Nat) :
    lucasLehmerTerm (n + 1) =
      lucasLehmerTerm n * lucasLehmerTerm n - 2 := by
  rfl

theorem lucasLehmerTerm_one :
    lucasLehmerTerm 1 = 14 := by
  rfl

theorem lucasLehmerTerm_two :
    lucasLehmerTerm 2 = 194 := by
  rfl

theorem lucasLehmerTerm_three :
    lucasLehmerTerm 3 = 37634 := by
  rfl

theorem lucasLehmerStepMod_zero_mod_seven :
    hsame (lucasLehmerStepMod MersenneThree BHist.Empty) (natToUnary 5) := by
  rfl

theorem natToUnary_append (m n : Nat) :
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

theorem natMulFn_natToUnary (m n : Nat) :
    natMulFn (natToUnary m) (natToUnary n) = natToUnary (m * n) := by
  induction n with
  | zero =>
      rw [Nat.mul_zero]
      rfl
  | succ n ih =>
      change append (natMulFn (natToUnary m) (natToUnary n)) (natToUnary m) =
        natToUnary (m * Nat.succ n)
      rw [ih]
      rw [natToUnary_append]
      rw [Nat.mul_succ]

theorem natToUnary_mul_rel (m n : Nat) :
    NatMul (natToUnary m) (natToUnary n) (natToUnary (m * n)) := by
  have rel :
      NatMul (natToUnary m) (natToUnary n)
        (natMulFn (natToUnary m) (natToUnary n)) :=
    natMulFn_rel (natToUnary_unary m) (natToUnary_unary n)
  exact (NatMul_result_hsame_transport rel (natMulFn_natToUnary m n)).right

theorem natDivides_natToUnary_of_factor (d q : Nat) :
    NatDivides (natToUnary d) (natToUnary (d * q)) :=
  ⟨natToUnary q, natToUnary_unary q, natToUnary_mul_rel d q⟩

theorem lucasLehmerStepMod_unary (M r : BHist) :
    UnaryHistory (lucasLehmerStepMod M r) := by
  unfold lucasLehmerStepMod
  exact natModFn_unary_all M (append (natMulFn r r) (natComplementMod M NatTwo))

theorem lucasLehmerResidueFuel_unary (M : BHist) (fuel : Nat) :
    UnaryHistory (lucasLehmerResidueFuel M fuel) := by
  induction fuel with
  | zero =>
      unfold lucasLehmerResidueFuel
      exact natModFn_unary_all M (natToUnary 4)
  | succ fuel ih =>
      unfold lucasLehmerResidueFuel
      exact lucasLehmerStepMod_unary M (lucasLehmerResidueFuel M fuel)

theorem lucasLehmerResidue_unary (p : Nat) :
    UnaryHistory (lucasLehmerResidue p) := by
  exact lucasLehmerResidueFuel_unary (mersenne p) (p - 2)

private theorem natOne_strict_of_tail (tail : BHist) :
    UnaryHistory tail -> (tail = BHist.Empty -> False) ->
      NatUnaryStrictPrefix (natToUnary 1) (BHist.e1 tail) := by
  intro tailUnary tailNonempty
  have shifted : append (natToUnary 1) tail = BHist.e1 tail :=
    (unary_append_e1_left (h := tail) (k := BHist.Empty) tailUnary).trans
      (congrArg BHist.e1 (append_empty_left tail))
  exact ⟨tail, tailUnary, tailNonempty, cont_intro shifted.symm⟩

private theorem natOne_strict_natToUnary_succ_succ (n : Nat) :
    NatUnaryStrictPrefix (natToUnary 1) (natToUnary (Nat.succ (Nat.succ n))) := by
  change NatUnaryStrictPrefix (natToUnary 1) (BHist.e1 (natToUnary (Nat.succ n)))
  exact natOne_strict_of_tail (natToUnary (Nat.succ n))
    (natToUnary_unary (Nat.succ n)) (fun empty => by
      change BHist.e1 (natToUnary n) = BHist.Empty at empty
      exact not_hsame_e1_empty empty)

theorem NatSeven_prime : NatPrime MersenneThree := by
  change NatPrime (natToUnary 7)
  exact minFactor_prime (natOne_strict_natToUnary_succ_succ 5)

theorem NatThirtyOne_prime : NatPrime MersenneFive := by
  change NatPrime (natToUnary 31)
  exact minFactor_prime (natOne_strict_natToUnary_succ_succ 29)

theorem NatOneTwentySeven_prime : NatPrime MersenneSeven := by
  change NatPrime (natToUnary 127)
  exact minFactor_prime (natOne_strict_natToUnary_succ_succ 125)

theorem NatOneTwentySeven_unary : UnaryHistory MersenneSeven := by
  exact natToUnary_unary 127

theorem lucasLehmerResidue_strict
    (p : Nat) (nonempty : hsame (mersenne p) BHist.Empty -> False) :
    NatUnaryStrictPrefix (lucasLehmerResidue p) (mersenne p) := by
  unfold lucasLehmerResidue
  induction p - 2 with
  | zero =>
      unfold lucasLehmerResidueFuel
      exact natModFn_strict_all (natToUnary_unary (mersenneNat p)) nonempty
  | succ fuel ih =>
      unfold lucasLehmerResidueFuel
      exact natModFn_strict_all (natToUnary_unary (mersenneNat p)) nonempty

def lucasLehmerResidueZMod (p : Nat)
    (nonempty : hsame (mersenne p) BHist.Empty -> False) : ZMod (mersenne p) :=
  { val := lucasLehmerResidue p
    isLt := lucasLehmerResidue_strict p nonempty }

theorem lucasLehmerResidueZMod_val (p : Nat)
    (nonempty : hsame (mersenne p) BHist.Empty -> False) :
    (lucasLehmerResidueZMod p nonempty).val = lucasLehmerResidue p := by
  rfl

theorem lucasLehmerResidueNat_three_zero :
    lucasLehmerResidueNat 3 = 0 := by
  rfl

theorem lucasLehmer_mersenne_three_divides :
    LucasLehmerDividesTerm 3 := by
  change NatDivides (natToUnary 7) (natToUnary 14)
  exact natDivides_natToUnary_of_factor 7 2

theorem lucasLehmerResidueNat_five_zero :
    lucasLehmerResidueNat 5 = 0 := by
  rfl

theorem lucasLehmerResidueNat_seven_zero :
    lucasLehmerResidueNat 7 = 0 := by
  rfl

end BEDC.Derived.LucasLehmerUp
