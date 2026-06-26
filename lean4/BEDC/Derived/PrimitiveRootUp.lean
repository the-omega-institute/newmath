import BEDC.Derived.EulerTheoremUp
import BEDC.Derived.PrimeUp.DivisionWithRemainder
import BEDC.Derived.PrimeUp.NatMulTransport

namespace BEDC.Derived.PrimitiveRootUp

open BEDC.Algebra.Rel
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.NatUp
open BEDC.Derived.IntUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModUp
open BEDC.Derived.EulerTheoremUp

variable {A : Type u} {r : A -> A -> Prop}

private theorem relPow_add (R : RelCommRing A r) (a : A) :
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

private theorem relPow_mul_period (R : RelCommRing A r) (a : A) {k : Nat} :
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
        (relPow_add R a (k * q) k)
        (R.trans
          (R.mul_congr ih period)
          (R.one_mul R.one))

private theorem relPow_drop_period_prefix
    (R : RelCommRing A r) (a : A) {k : Nat} :
    r (relPow R a k) R.one ->
      ∀ q rest : Nat,
        r (relPow R a (k * q + rest)) (relPow R a rest) := by
  intro period q rest
  exact R.trans
    (relPow_add R a (k * q) rest)
    (R.trans
      (R.mul_congr (relPow_mul_period R a period q) (R.refl (relPow R a rest)))
      (R.one_mul (relPow R a rest)))

private theorem unary_nonempty_length_positive {h : BHist} :
    UnaryHistory h -> (h = BHist.Empty -> False) -> 0 < bwordLength h := by
  intro hUnary hNonempty
  cases h with
  | Empty =>
      exact False.elim (hNonempty rfl)
  | e0 h =>
      cases hUnary
  | e1 h =>
      change 0 < Nat.succ (bwordLength h)
      exact Nat.succ_pos (bwordLength h)

private theorem NatUnaryStrictPrefix_length_lt {r k : BHist} :
    UnaryHistory k -> NatUnaryStrictPrefix r k -> bwordLength r < bwordLength k := by
  intro kUnary strict
  cases strict with
  | intro tail tailData =>
      have rUnary : UnaryHistory r :=
        unary_cont_left_factor tailData.right.right kUnary
      have tailPositive : 0 < bwordLength tail :=
        unary_nonempty_length_positive tailData.left tailData.right.left
      have lengthK :
          bwordLength k = bwordLength r + bwordLength tail :=
        NatUp_unary_standard_bridge.right.right.right.right rUnary
          tailData.left tailData.right.right
      rw [lengthK]
      exact Nat.lt_add_of_pos_right tailPositive

def PowerOneAtNat
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) (k : Nat) : Prop :=
  zmodEq (zmodPowByNat n nUnary nNonempty a k)
    (zmodOne n nUnary nNonempty)

structure HasMultOrder
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) (k : BHist) where
  k_unary : UnaryHistory k
  k_positive : 0 < bwordLength k
  pow_one : PowerOneAtNat n nUnary nNonempty a (bwordLength k)
  minimal :
    ∀ j : Nat, 0 < j -> j < bwordLength k ->
      PowerOneAtNat n nUnary nNonempty a j -> False

def IsPrimitiveRoot
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (phi : BHist) (g : ZMod n) : Prop :=
  HasMultOrder n nUnary nNonempty g phi

private def powEqOneBool
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) (k : Nat) : Bool :=
  if (zmodPowByNat n nUnary nNonempty a k).val =
      (zmodOne n nUnary nNonempty).val then true else false

def multOrderSearchFrom
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) : Nat -> Nat -> Option Nat
  | _start, 0 => none
  | start, fuel + 1 =>
      if powEqOneBool n nUnary nNonempty a start then
        some start
      else
        multOrderSearchFrom n nUnary nNonempty a (start + 1) fuel

def multOrder
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) : BHist :=
  match multOrderSearchFrom n nUnary nNonempty a 1 (bwordLength n + 1) with
  | some k => natToUnary k
  | none => BHist.Empty

theorem multOrder_divides_phi
    {n k phi : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n)
    (order : HasMultOrder n nUnary nNonempty a k)
    (phiUnary : UnaryHistory phi)
    (phiPow : PowerOneAtNat n nUnary nNonempty a (bwordLength phi)) :
    NatDivides k phi := by
  let period : Nat := bwordLength k
  have kNonempty : hsame k BHist.Empty -> False := by
    intro same
    cases same
    exact Nat.not_lt_zero 0 order.k_positive
  have divrem : ∃ q : BHist, ∃ r : BHist, NatDivRem k phi q r :=
    divRem_exists order.k_unary phiUnary kNonempty
  cases divrem with
  | intro q qRest =>
  cases qRest with
  | intro remainder divremData =>
  cases divremData with
  | intro product productData =>
  have periodPow :
      zmodEq (zmodPowByNat n nUnary nNonempty a period)
        (zmodOne n nUnary nNonempty) := by
    unfold period
    exact order.pow_one
  have dropRemainder :
      zmodEq
        (zmodPowByNat n nUnary nNonempty a
          (period * bwordLength q + bwordLength remainder))
        (zmodPowByNat n nUnary nNonempty a (bwordLength remainder)) := by
    unfold zmodPowByNat at periodPow
    unfold zmodPowByNat
    exact relPow_drop_period_prefix
      (zmodRelCommRing n nUnary nNonempty) a periodPow
      (bwordLength q) (bwordLength remainder)
  have decomposition :
      period * bwordLength q + bwordLength remainder = bwordLength phi := by
    unfold period
    rw [← NatMul_bwordLength productData.left]
    exact (NatAdd_length productData.right.left).symm
  have sumPowOne :
      zmodEq
        (zmodPowByNat n nUnary nNonempty a
          (period * bwordLength q + bwordLength remainder))
        (zmodOne n nUnary nNonempty) := by
    have samePow :
        zmodEq
          (zmodPowByNat n nUnary nNonempty a
            (period * bwordLength q + bwordLength remainder))
          (zmodPowByNat n nUnary nNonempty a (bwordLength phi)) := by
      rw [decomposition]
      exact zmodEq_refl _
    exact zmodEq_trans samePow phiPow
  have remainderPow :
      PowerOneAtNat n nUnary nNonempty a (bwordLength remainder) := by
    unfold PowerOneAtNat
    exact zmodEq_trans (zmodEq_symm dropRemainder) sumPowOne
  have remainderEmpty : hsame remainder BHist.Empty := by
    cases remainder with
    | Empty =>
        rfl
    | e0 tail =>
        cases NatAdd_right_unary productData.right.left
    | e1 tail =>
        have remainderPositive : 0 < bwordLength (BHist.e1 tail) := by
          change 0 < Nat.succ (bwordLength tail)
          exact Nat.succ_pos (bwordLength tail)
        have remainderLt : bwordLength (BHist.e1 tail) < period := by
          unfold period
          exact NatUnaryStrictPrefix_length_lt order.k_unary productData.right.right
        exact False.elim
          (order.minimal (bwordLength (BHist.e1 tail))
            remainderPositive remainderLt remainderPow)
  have sameProductPhi : hsame product phi := by
    cases remainderEmpty
    exact hsame_symm
      (cont_deterministic productData.right.left.right.right
        (cont_right_unit product))
  have shiftedProduct :=
    NatMul_result_hsame_transport productData.left sameProductPhi
  exact ⟨q, NatMul_right_unary productData.left, shiftedProduct.right⟩

abbrev NatTwo : BHist := natToUnary 2
abbrev NatFour : BHist := natToUnary 4
abbrev NatFive : BHist := natToUnary 5

private def NatFive_nonempty : hsame NatFive BHist.Empty -> False := by
  intro empty
  unfold NatFive natToUnary at empty
  cases empty

def twoModFive : ZMod NatFive :=
  zmodFromNat NatFive (natToUnary_unary 5) NatFive_nonempty
    NatTwo (natToUnary_unary 2)

private theorem two_mod_five_not_pow_one_at_one :
    PowerOneAtNat NatFive (natToUnary_unary 5) NatFive_nonempty
      twoModFive 1 -> False := by
  intro pow
  unfold PowerOneAtNat zmodPowByNat twoModFive zmodFromNat zmodOne zmodEq at pow
  change hsame
    (natModFn NatFive (natMulFn NatOne NatTwo))
    (natModFn NatFive NatOne) at pow
  unfold NatFive NatTwo NatOne natToUnary natMulFn natModFn at pow
  cases pow

private theorem two_mod_five_not_pow_one_at_two :
    PowerOneAtNat NatFive (natToUnary_unary 5) NatFive_nonempty
      twoModFive 2 -> False := by
  intro pow
  unfold PowerOneAtNat zmodPowByNat twoModFive zmodFromNat zmodOne zmodEq at pow
  unfold NatFive NatTwo NatOne natToUnary natMulFn natModFn at pow
  cases pow

private theorem two_mod_five_not_pow_one_at_three :
    PowerOneAtNat NatFive (natToUnary_unary 5) NatFive_nonempty
      twoModFive 3 -> False := by
  intro pow
  unfold PowerOneAtNat zmodPowByNat twoModFive zmodFromNat zmodOne zmodEq at pow
  unfold NatFive NatTwo NatOne natToUnary natMulFn natModFn at pow
  cases pow

private theorem two_mod_five_minimal :
    ∀ j : Nat, 0 < j -> j < bwordLength NatFour ->
      PowerOneAtNat NatFive (natToUnary_unary 5) NatFive_nonempty
        twoModFive j -> False := by
  intro j jPositive jLt pow
  cases j with
  | zero =>
      exact Nat.not_lt_zero 0 jPositive
  | succ j1 =>
      cases j1 with
      | zero =>
          exact two_mod_five_not_pow_one_at_one pow
      | succ j2 =>
          cases j2 with
          | zero =>
              exact two_mod_five_not_pow_one_at_two pow
          | succ j3 =>
              cases j3 with
              | zero =>
                  exact two_mod_five_not_pow_one_at_three pow
              | succ j4 =>
                  change Nat.succ (Nat.succ (Nat.succ (Nat.succ j4))) < 4 at jLt
                  have ltThree :
                      Nat.succ (Nat.succ (Nat.succ j4)) < 3 :=
                    Nat.succ_lt_succ_iff.mp jLt
                  have ltTwo : Nat.succ (Nat.succ j4) < 2 :=
                    Nat.succ_lt_succ_iff.mp ltThree
                  have ltOne : Nat.succ j4 < 1 :=
                    Nat.succ_lt_succ_iff.mp ltTwo
                  have ltZero : j4 < 0 :=
                    Nat.succ_lt_succ_iff.mp ltOne
                  exact Nat.not_lt_zero j4 ltZero

theorem two_mod_five_has_order_four :
    HasMultOrder NatFive (natToUnary_unary 5) NatFive_nonempty
      twoModFive NatFour where
  k_unary := natToUnary_unary 4
  k_positive := by
    change 0 < 4
    exact Nat.succ_pos 3
  pow_one := by
    unfold PowerOneAtNat zmodPowByNat twoModFive zmodFromNat zmodOne zmodEq
    unfold NatFive NatTwo NatOne natToUnary natMulFn natModFn
    rfl
  minimal := two_mod_five_minimal

theorem two_mod_five_is_primitive_root :
    IsPrimitiveRoot NatFive (natToUnary_unary 5) NatFive_nonempty
      NatFour twoModFive :=
  two_mod_five_has_order_four

theorem two_mod_five_multOrder :
    hsame
      (multOrder NatFive (natToUnary_unary 5) NatFive_nonempty twoModFive)
      NatFour := by
  rfl

end BEDC.Derived.PrimitiveRootUp
