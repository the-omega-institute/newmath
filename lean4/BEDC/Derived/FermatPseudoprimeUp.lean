import BEDC.Derived.CarmichaelNumberUp
import BEDC.Derived.FermatLittleUp
import BEDC.Derived.PrimitiveRootUp

set_option maxRecDepth 10000

namespace BEDC.Derived.FermatPseudoprimeUp

open BEDC.Algebra.Rel
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.CarmichaelNumberUp
open BEDC.Derived.CarmichaelUp
open BEDC.Derived.EulerTheoremUp
open BEDC.Derived.GcdUp
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PrimitiveRootUp
open BEDC.Derived.ZModUp

abbrev NatOne : BHist := BEDC.Derived.PadicUp.NatOne
abbrev NatTwo : BHist := natToUnary 2
abbrev NatEleven : BHist := natToUnary 11
abbrev NatThirtyOne : BHist := natToUnary 31
abbrev NatThreeHundredFortyOne : BHist := natToUnary 341

def BaseFermatCongruence
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) : Prop :=
  zmodEq
    (zmodPowByNat n nUnary nNonempty a (bwordLength n - 1))
    (zmodOne n nUnary nNonempty)

def FermatPseudoprimeBase
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) : Prop :=
  CompositeNumber n ∧ NatGcd a.val n NatOne ∧
    BaseFermatCongruence n nUnary nNonempty a

def FermatPseudoprime (n a : BHist) : Prop :=
  ∃ nUnary : UnaryHistory n, ∃ nNonempty : hsame n BHist.Empty -> False,
    ∃ aUnary : UnaryHistory a,
      FermatPseudoprimeBase n nUnary nNonempty
        (zmodFromNat n nUnary nNonempty a aUnary)

def AllCoprimeBasesFermat
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) : Prop :=
  ∀ a : ZMod n, NatGcd a.val n NatOne ->
    BaseFermatCongruence n nUnary nNonempty a

def CarmichaelAsAllBasePseudoprime (n : BHist) : Prop :=
  ∃ nUnary : UnaryHistory n, ∃ nNonempty : hsame n BHist.Empty -> False,
    CompositeNumber n ∧ AllCoprimeBasesFermat n nUnary nNonempty

theorem carmichaelResidueCondition_iff_allCoprimeBasesFermat
    {n : BHist} {nUnary : UnaryHistory n}
    {nNonempty : hsame n BHist.Empty -> False} :
    CarmichaelNumberUp.CarmichaelResidueCondition n nUnary nNonempty ↔
      AllCoprimeBasesFermat n nUnary nNonempty := by
  rfl

theorem carmichaelNumber_iff_allBasePseudoprime {n : BHist} :
    CarmichaelNumberUp.CarmichaelNumber n ↔ CarmichaelAsAllBasePseudoprime n := by
  constructor
  · intro carmichael
    cases carmichael with
    | intro nUnary rest =>
        cases rest with
        | intro nNonempty data =>
            exact ⟨nUnary, nNonempty, data.left, data.right⟩
  · intro allBase
    cases allBase with
    | intro nUnary rest =>
        cases rest with
        | intro nNonempty data =>
            exact ⟨nUnary, nNonempty, data.left, data.right⟩

theorem carmichaelNumber_base_pseudoprime
    {n : BHist} (carmichael : CarmichaelNumberUp.CarmichaelNumber n)
    (a : ZMod n) :
    NatGcd a.val n NatOne ->
      ∃ nUnary : UnaryHistory n, ∃ nNonempty : hsame n BHist.Empty -> False,
        FermatPseudoprimeBase n nUnary nNonempty a := by
  intro gcd
  cases carmichael with
  | intro nUnary rest =>
      cases rest with
      | intro nNonempty data =>
          exact ⟨nUnary, nNonempty, data.left, gcd, data.right a gcd⟩

private theorem natOne_strict_of_tail (tail : BHist) :
    UnaryHistory tail -> (tail = BHist.Empty -> False) ->
      NatUnaryStrictPrefix NatOne (BHist.e1 tail) := by
  intro tailUnary tailNonempty
  have shifted : append NatOne tail = BHist.e1 tail :=
    (unary_append_e1_left (h := tail) (k := BHist.Empty) tailUnary).trans
      (congrArg BHist.e1 (append_empty_left tail))
  exact ⟨tail, tailUnary, tailNonempty, cont_intro shifted.symm⟩

private theorem NatOne_strict_natToUnary_succ_succ (n : Nat) :
    NatUnaryStrictPrefix NatOne (natToUnary (Nat.succ (Nat.succ n))) := by
  change NatUnaryStrictPrefix NatOne (BHist.e1 (natToUnary (Nat.succ n)))
  exact natOne_strict_of_tail (natToUnary (Nat.succ n))
    (natToUnary_unary (Nat.succ n)) (fun empty => by
      change BHist.e1 (natToUnary n) = BHist.Empty at empty
      exact not_hsame_e1_empty empty)

private theorem natToUnary_mul_rel (a b : Nat) :
    NatMul (natToUnary a) (natToUnary b) (natToUnary (a * b)) := by
  have total := NatMul_total (natToUnary_unary a) (natToUnary_unary b)
  cases total with
  | intro result resultData =>
      have sameResult : hsame result (natToUnary (a * b)) :=
        (NatUp_unary_standard_bridge.right.right.right.left
          resultData.left (natToUnary_unary _)).mpr (by
            rw [NatMul_bwordLength resultData.right]
            rw [natToUnary_length, natToUnary_length, natToUnary_length])
      exact (NatMul_result_hsame_transport resultData.right sameResult).right

theorem NatEleven_mul_NatThirtyOne :
    NatMul NatEleven NatThirtyOne NatThreeHundredFortyOne := by
  exact natToUnary_mul_rel 11 31

theorem NatThreeHundredFortyOne_unary :
    UnaryHistory NatThreeHundredFortyOne := by
  exact natToUnary_unary 341

theorem NatThreeHundredFortyOne_nonempty :
    hsame NatThreeHundredFortyOne BHist.Empty -> False := by
  intro empty
  unfold NatThreeHundredFortyOne natToUnary at empty
  exact not_hsame_e1_empty empty

theorem NatThreeHundredFortyOne_composite :
    CompositeNumber NatThreeHundredFortyOne := by
  constructor
  · exact NatThreeHundredFortyOne_unary
  · constructor
    · exact NatOne_strict_natToUnary_succ_succ 339
    · exact ⟨NatEleven, NatThirtyOne,
        natToUnary_unary 11, natToUnary_unary 31,
        NatOne_strict_natToUnary_succ_succ 9,
        NatOne_strict_natToUnary_succ_succ 29,
        NatEleven_mul_NatThirtyOne⟩

def twoModThreeHundredFortyOne : ZMod NatThreeHundredFortyOne :=
  zmodFromNat NatThreeHundredFortyOne NatThreeHundredFortyOne_unary
    NatThreeHundredFortyOne_nonempty
    NatTwo (natToUnary_unary 2)

theorem NatTwo_coprime_NatThreeHundredFortyOne :
    NatGcd NatTwo NatThreeHundredFortyOne NatOne := by
  have gcdFn :
      NatGcd NatTwo NatThreeHundredFortyOne
        (natGcdFn NatTwo NatThreeHundredFortyOne) :=
    natGcdFn_spec (natToUnary_unary 2) (natToUnary_unary 341)
  have gcdEq : hsame (natGcdFn NatTwo NatThreeHundredFortyOne) NatOne := by
    rfl
  constructor
  · exact NatGcd_left_unary gcdFn
  · constructor
    · exact NatGcd_right_unary gcdFn
    · constructor
      · exact unary_e1_closed unary_empty
      · constructor
        · exact (NatDivides_divisor_hsame_transport
            (NatGcd_dvd_left gcdFn) gcdEq).right
        · constructor
          · exact (NatDivides_divisor_hsame_transport
              (NatGcd_dvd_right gcdFn) gcdEq).right
          · intro d dividesTwo dividesN
            exact (NatDivides_dividend_hsame_transport
              (NatGcd_greatest gcdFn dividesTwo dividesN) gcdEq).right

def powModNat (base : Nat) : Nat -> Nat -> Nat
  | 0, modulus => 1 % modulus
  | exponent + 1, modulus => (powModNat base exponent modulus * base) % modulus

def CompositeNat (n : Nat) : Prop :=
  ∃ d e : Nat, 1 < d ∧ 1 < e ∧ n = d * e

def FermatPseudoprimeBaseNat (n a : Nat) : Prop :=
  CompositeNat n ∧ 1 < a ∧ powModNat a (n - 1) n = 1

theorem powModNat_two_340_341 :
    powModNat 2 340 341 = 1 := by
  decide

theorem NatThreeHundredFortyOne_base_two_pseudoprime_nat :
    FermatPseudoprimeBaseNat 341 2 := by
  exact ⟨⟨11, 31, by decide, by decide, by decide⟩,
    by decide, powModNat_two_340_341⟩

private theorem NatUnaryStrictPrefix_of_length_lt_local {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h < bwordLength k ->
      NatUnaryStrictPrefix h k := by
  intro hUnary kUnary lengthLt
  have total := NatUnaryPrefix_total hUnary kUnary
  cases total with
  | inl left =>
      cases left with
      | intro tail tailData =>
          cases NatUnaryPrefix_cont_tail_cases tailData.left tailData.right with
          | inl same =>
              have lengthEq : bwordLength h = bwordLength k :=
                (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mp same
              rw [lengthEq] at lengthLt
              exact False.elim (Nat.lt_irrefl _ lengthLt)
          | inr strict =>
              exact strict
  | inr right =>
      cases right with
      | intro tail tailData =>
          cases NatUnaryPrefix_cont_tail_cases tailData.left tailData.right with
          | inl same =>
              have lengthEq : bwordLength h = bwordLength k :=
                (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mp
                  (hsame_symm same)
              rw [lengthEq] at lengthLt
              exact False.elim (Nat.lt_irrefl _ lengthLt)
          | inr strictKH =>
              have kLtH := NatUnaryStrictPrefix_length_lt kUnary strictKH
              exact False.elim (Nat.lt_asymm lengthLt kLtH)

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

private theorem natToUnary_add_rel (a b : Nat) :
    NatAdd (natToUnary a) (natToUnary b) (natToUnary (a + b)) := by
  exact ⟨natToUnary_unary a, natToUnary_unary b,
    cont_intro (natToUnary_append a b).symm⟩

def natPowHist (a : BHist) : Nat -> BHist
  | 0 => NatOne
  | exponent + 1 => natMulFn (natPowHist a exponent) a

private theorem natPowHist_unary {a : BHist} :
    UnaryHistory a -> ∀ exponent : Nat, UnaryHistory (natPowHist a exponent)
  | _aUnary, 0 =>
      unary_e1_closed unary_empty
  | aUnary, exponent + 1 =>
      natMulFn_unary (natPowHist_unary aUnary exponent) aUnary

def natPowStd (a : Nat) : Nat -> Nat
  | 0 => 1
  | exponent + 1 => natPowStd a exponent * a

private theorem natMulFn_natToUnary_hsame (a b : Nat) :
    hsame (natMulFn (natToUnary a) (natToUnary b))
      (natToUnary (a * b)) := by
  exact NatMul_functional (natToUnary_unary a)
    (natMulFn_rel (natToUnary_unary a) (natToUnary_unary b))
    (natToUnary_mul_rel a b)

private theorem natPowHist_natToUnary_hsame (a exponent : Nat) :
    hsame (natPowHist (natToUnary a) exponent)
      (natToUnary (natPowStd a exponent)) := by
  induction exponent with
  | zero =>
      rfl
  | succ exponent ih =>
      change hsame
        (natMulFn (natPowHist (natToUnary a) exponent) (natToUnary a))
        (natToUnary (natPowStd a exponent * a))
      exact hsame_trans
        (natMulFn_hsame_transport ih (hsame_refl (natToUnary a)))
        (natMulFn_natToUnary_hsame (natPowStd a exponent) a)

private theorem natPowStd_two_ten :
    natPowStd 2 10 = 1024 := by
  decide

theorem natPowHist_two_ten :
    hsame (natPowHist NatTwo 10) (natToUnary 1024) := by
  unfold NatTwo
  exact hsame_trans (natPowHist_natToUnary_hsame 2 10)
    (by
      rw [natPowStd_two_ten]
      exact hsame_refl (natToUnary 1024))

private theorem natModFn_eq_of_natDivRem {M n q r : BHist} :
    UnaryHistory M -> UnaryHistory n -> (hsame M BHist.Empty -> False) ->
      NatDivRem M n q r -> hsame (natModFn M n) r := by
  intro MUnary nUnary MNonempty divrem
  exact (natModFn_unique MUnary nUnary MNonempty divrem).right

theorem two_pow_ten_raw_mod_341 :
    hsame
      (natModFn NatThreeHundredFortyOne (natToUnary 1024))
      NatOne := by
  have mul :
      NatMul NatThreeHundredFortyOne (natToUnary 3) (natToUnary 1023) := by
    exact natToUnary_mul_rel 341 3
  have add :
      NatAdd (natToUnary 1023) NatOne (natToUnary 1024) := by
    exact natToUnary_add_rel 1023 1
  have strict :
      NatUnaryStrictPrefix NatOne NatThreeHundredFortyOne :=
    NatUnaryStrictPrefix_of_length_lt_local
      (unary_e1_closed unary_empty) NatThreeHundredFortyOne_unary (by
        rw [natToUnary_length]
        decide)
  have divrem :
      NatDivRem NatThreeHundredFortyOne (natToUnary 1024)
        (natToUnary 3) NatOne :=
    ⟨natToUnary 1023, mul, add, strict⟩
  exact natModFn_eq_of_natDivRem NatThreeHundredFortyOne_unary
    (natToUnary_unary 1024) NatThreeHundredFortyOne_nonempty divrem

theorem zmodPowByNat_fromNat_val {n a : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (aUnary : UnaryHistory a) :
    ∀ exponent : Nat,
      hsame
        (zmodPowByNat n nUnary nNonempty
          (zmodFromNat n nUnary nNonempty a aUnary) exponent).val
        (natModFn n (natPowHist a exponent))
  | 0 =>
      rfl
  | exponent + 1 => by
      change hsame
        (natModFn n
          (natMulFn
            (zmodPowByNat n nUnary nNonempty
              (zmodFromNat n nUnary nNonempty a aUnary) exponent).val
            (natModFn n a)))
        (natModFn n (natMulFn (natPowHist a exponent) a))
      have tail :
          hsame
            (zmodPowByNat n nUnary nNonempty
              (zmodFromNat n nUnary nNonempty a aUnary) exponent).val
            (natModFn n (natPowHist a exponent)) :=
        zmodPowByNat_fromNat_val nUnary nNonempty aUnary exponent
      have reduced :
          hsame
            (natModFn n
              (natMulFn
                (zmodPowByNat n nUnary nNonempty
                  (zmodFromNat n nUnary nNonempty a aUnary) exponent).val
                (natModFn n a)))
            (natModFn n
              (natMulFn (natModFn n (natPowHist a exponent))
                (natModFn n a))) :=
        natModFn_hsame_arg_transport (M := n)
          (natMulFn_hsame_transport tail (hsame_refl (natModFn n a)))
      have raw :
          hsame
            (natModFn n (natMulFn (natPowHist a exponent) a))
            (natModFn n
              (natMulFn (natModFn n (natPowHist a exponent))
                (natModFn n a))) :=
        mod_mul_compat nUnary nNonempty
          (natPowHist_unary aUnary exponent) aUnary
      exact hsame_trans reduced (hsame_symm raw)

private theorem relPow_add_local {A : Type u} {r : A -> A -> Prop}
    (R : RelCommRing A r) (a : A) :
    ∀ m n : Nat,
      r (relPow R a (m + n)) (R.mul (relPow R a m) (relPow R a n)) := by
  intro m n
  induction n with
  | zero =>
      change r (relPow R a m) (R.mul (relPow R a m) R.one)
      exact R.symm (R.mul_one (relPow R a m))
  | succ n ih =>
      change r (R.mul (relPow R a (m + n)) a)
        (R.mul (relPow R a m) (R.mul (relPow R a n) a))
      exact R.trans
        (R.mul_congr ih (R.refl a))
        (R.mul_assoc (relPow R a m) (relPow R a n) a)

private theorem relPow_mul_period_local {A : Type u} {r : A -> A -> Prop}
    (R : RelCommRing A r) (a : A) {k : Nat} :
    r (relPow R a k) R.one ->
      ∀ q : Nat, r (relPow R a (k * q)) R.one := by
  intro period q
  induction q with
  | zero =>
      change r R.one R.one
      exact R.refl R.one
  | succ q ih =>
      rw [Nat.mul_succ]
      exact R.trans
        (relPow_add_local R a (k * q) k)
        (R.trans
          (R.mul_congr ih period)
          (R.one_mul R.one))

theorem two_pow_ten_mod_341 :
    zmodEq
      (zmodPowByNat NatThreeHundredFortyOne (natToUnary_unary 341)
        NatThreeHundredFortyOne_nonempty
        twoModThreeHundredFortyOne 10)
      (zmodOne NatThreeHundredFortyOne (natToUnary_unary 341)
        NatThreeHundredFortyOne_nonempty) := by
  have oneMod :
      hsame (natModFn NatThreeHundredFortyOne NatOne) NatOne := by
    exact natModFn_of_strict NatThreeHundredFortyOne_unary
      NatThreeHundredFortyOne_nonempty (unary_e1_closed unary_empty)
      (NatUnaryStrictPrefix_of_length_lt_local
        (unary_e1_closed unary_empty) NatThreeHundredFortyOne_unary (by
          rw [natToUnary_length]
          decide))
  have twoMod :
      hsame (natModFn NatThreeHundredFortyOne NatTwo) NatTwo := by
    exact natModFn_of_strict NatThreeHundredFortyOne_unary
      NatThreeHundredFortyOne_nonempty (natToUnary_unary 2)
      (NatUnaryStrictPrefix_of_length_lt_local
        (natToUnary_unary 2) NatThreeHundredFortyOne_unary (by
          rw [natToUnary_length, natToUnary_length]
          decide))
  have powVal :
      hsame
        (zmodPowByNat NatThreeHundredFortyOne (natToUnary_unary 341)
          NatThreeHundredFortyOne_nonempty
          twoModThreeHundredFortyOne 10).val
        (natModFn NatThreeHundredFortyOne (natPowHist NatTwo 10)) :=
    zmodPowByNat_fromNat_val NatThreeHundredFortyOne_unary
      NatThreeHundredFortyOne_nonempty (natToUnary_unary 2) 10
  have rawMod :
      hsame
        (natModFn NatThreeHundredFortyOne (natPowHist NatTwo 10))
        NatOne :=
    hsame_trans
      (natModFn_hsame_arg_transport (M := NatThreeHundredFortyOne)
        natPowHist_two_ten)
      two_pow_ten_raw_mod_341
  exact hsame_trans powVal (hsame_trans rawMod (hsame_symm oneMod))

theorem two_pow_340_mod_341 :
    BaseFermatCongruence NatThreeHundredFortyOne
      (natToUnary_unary 341)
      NatThreeHundredFortyOne_nonempty
      twoModThreeHundredFortyOne := by
  unfold BaseFermatCongruence
  rw [natToUnary_length]
  change zmodEq
    (zmodPowByNat NatThreeHundredFortyOne (natToUnary_unary 341)
      NatThreeHundredFortyOne_nonempty
      twoModThreeHundredFortyOne 340)
    (zmodOne NatThreeHundredFortyOne (natToUnary_unary 341)
      NatThreeHundredFortyOne_nonempty)
  let R := zmodRelCommRing NatThreeHundredFortyOne (natToUnary_unary 341)
    NatThreeHundredFortyOne_nonempty
  have period :
      zmodEq
        (relPow R twoModThreeHundredFortyOne 10)
        R.one := by
    exact two_pow_ten_mod_341
  have repeated :
      zmodEq
        (relPow R twoModThreeHundredFortyOne (10 * 34))
        R.one :=
    relPow_mul_period_local R twoModThreeHundredFortyOne period 34
  exact repeated

theorem NatThreeHundredFortyOne_base_two_pseudoprime :
    FermatPseudoprimeBase NatThreeHundredFortyOne
      (natToUnary_unary 341)
      NatThreeHundredFortyOne_nonempty
      twoModThreeHundredFortyOne := by
  exact ⟨NatThreeHundredFortyOne_composite,
    NatTwo_coprime_NatThreeHundredFortyOne,
    two_pow_340_mod_341⟩

theorem NatThreeHundredFortyOne_base_two_pseudoprime_hist :
    FermatPseudoprime NatThreeHundredFortyOne NatTwo := by
  exact ⟨natToUnary_unary 341,
    NatThreeHundredFortyOne_nonempty,
    natToUnary_unary 2,
    NatThreeHundredFortyOne_base_two_pseudoprime⟩

end BEDC.Derived.FermatPseudoprimeUp
