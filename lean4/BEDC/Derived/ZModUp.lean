import BEDC.Derived.PadicUp.IntegerTower.RingCompletion

namespace BEDC.Derived.ZModUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp

abbrev ZMod (n : BHist) : Type :=
  BoundedNat n

def zmodEq {n : BHist} (x y : ZMod n) : Prop :=
  hsame x.val y.val

theorem zmod_carrier_is_bounded (n : BHist) :
    ZMod n = BoundedNat n := by
  rfl

theorem zmodEq_refl {n : BHist} (x : ZMod n) : zmodEq x x := by
  rfl

theorem zmodEq_symm {n : BHist} {x y : ZMod n} :
    zmodEq x y -> zmodEq y x := by
  intro same
  exact hsame_symm same

theorem zmodEq_trans {n : BHist} {x y z : ZMod n} :
    zmodEq x y -> zmodEq y z -> zmodEq x z := by
  intro sameXY sameYZ
  exact hsame_trans sameXY sameYZ

theorem zmodVal_unary {n : BHist} (nUnary : UnaryHistory n) (x : ZMod n) :
    UnaryHistory x.val :=
  BoundedNat_unary nUnary x

def zmodFromNat (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (a : BHist) (aUnary : UnaryHistory a) :
    ZMod n :=
  { val := natModFn n a
    isLt := natModFn_lt nUnary aUnary nNonempty }

theorem zmodFromNat_spec {n a : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (aUnary : UnaryHistory a) :
    NatDivRem n a (natQuotFn n a) (zmodFromNat n nUnary nNonempty a aUnary).val := by
  exact natModFn_spec nUnary aUnary nNonempty

def zmodZero (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) : ZMod n :=
  { val := BHist.Empty
    isLt := ⟨n, nUnary, nNonempty, cont_left_unit n⟩ }

def zmodOne (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) : ZMod n :=
  { val := natModFn n NatOne
    isLt := natModFn_lt nUnary (unary_e1_closed unary_empty) nNonempty }

def zmodAdd (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x y : ZMod n) : ZMod n :=
  { val := natModFn n (append x.val y.val)
    isLt :=
      natModFn_lt nUnary
        (unary_append_closed (zmodVal_unary nUnary x) (zmodVal_unary nUnary y))
        nNonempty }

def zmodMul (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x y : ZMod n) : ZMod n :=
  { val := natModFn n (natMulFn x.val y.val)
    isLt :=
      natModFn_lt nUnary
        (natMulFn_unary (zmodVal_unary nUnary x) (zmodVal_unary nUnary y))
        nNonempty }

def zmodNeg (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x : ZMod n) : ZMod n :=
  { val := natComplementMod n x.val
    isLt := by
      unfold natComplementMod
      exact natModFn_lt nUnary (natSubUnary_unary nUnary) nNonempty }

theorem zmodAdd_congr {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) {x x' y y' : ZMod n} :
    zmodEq x x' -> zmodEq y y' ->
      zmodEq (zmodAdd n nUnary nNonempty x y)
        (zmodAdd n nUnary nNonempty x' y') := by
  intro sameX sameY
  exact natModFn_append_hsame_transport sameX sameY

theorem zmodMul_congr {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) {x x' y y' : ZMod n} :
    zmodEq x x' -> zmodEq y y' ->
      zmodEq (zmodMul n nUnary nNonempty x y)
        (zmodMul n nUnary nNonempty x' y') := by
  intro sameX sameY
  exact natModFn_hsame_arg_transport (M := n)
    (natMulFn_hsame_transport sameX sameY)

theorem zmodNeg_congr {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) {x y : ZMod n} :
    zmodEq x y ->
      zmodEq (zmodNeg n nUnary nNonempty x) (zmodNeg n nUnary nNonempty y) := by
  intro same
  exact natComplementMod_hsame_arg_transport same

theorem zmodAdd_comm {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x y : ZMod n) :
    zmodEq (zmodAdd n nUnary nNonempty x y)
      (zmodAdd n nUnary nNonempty y x) := by
  exact natModFn_hsame_arg_transport (M := n)
    (unary_append_comm (zmodVal_unary nUnary x) (zmodVal_unary nUnary y))

theorem zmodAdd_assoc {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x y z : ZMod n) :
    zmodEq (zmodAdd n nUnary nNonempty (zmodAdd n nUnary nNonempty x y) z)
      (zmodAdd n nUnary nNonempty x (zmodAdd n nUnary nNonempty y z)) := by
  change hsame
    (natModFn n (append (natModFn n (append x.val y.val)) z.val))
    (natModFn n (append x.val (natModFn n (append y.val z.val))))
  have xUnary : UnaryHistory x.val := zmodVal_unary nUnary x
  have yUnary : UnaryHistory y.val := zmodVal_unary nUnary y
  have zUnary : UnaryHistory z.val := zmodVal_unary nUnary z
  have xyUnary : UnaryHistory (append x.val y.val) :=
    unary_append_closed xUnary yUnary
  have yzUnary : UnaryHistory (append y.val z.val) :=
    unary_append_closed yUnary zUnary
  have leftToRaw :
      hsame
        (natModFn n (append (natModFn n (append x.val y.val)) z.val))
        (natModFn n (append (append x.val y.val) z.val)) := by
    exact hsame_symm
      (natModFn_add_congruence nUnary nNonempty
        xyUnary zUnary (natModFn_unary nUnary xyUnary nNonempty) zUnary
        (hsame_symm (mod_idem nUnary nNonempty xyUnary)) (hsame_refl _))
  have rawAssoc :
      hsame
        (natModFn n (append (append x.val y.val) z.val))
        (natModFn n (append x.val (append y.val z.val))) :=
    natModFn_hsame_arg_transport (M := n) (append_assoc x.val y.val z.val)
  have rawToRight :
      hsame
        (natModFn n (append x.val (append y.val z.val)))
        (natModFn n (append x.val (natModFn n (append y.val z.val)))) := by
    exact natModFn_add_congruence nUnary nNonempty
      xUnary yzUnary xUnary (natModFn_unary nUnary yzUnary nNonempty)
      (hsame_refl _) (hsame_symm (mod_idem nUnary nNonempty yzUnary))
  exact hsame_trans leftToRaw (hsame_trans rawAssoc rawToRight)

theorem zmodZero_add_left {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x : ZMod n) :
    zmodEq (zmodAdd n nUnary nNonempty (zmodZero n nUnary nNonempty) x) x := by
  change hsame (natModFn n (append BHist.Empty x.val)) x.val
  have xUnary : UnaryHistory x.val := zmodVal_unary nUnary x
  have dropZero :
      hsame (natModFn n (append BHist.Empty x.val)) (natModFn n x.val) :=
    natModFn_hsame_arg_transport (M := n) (append_empty_left x.val)
  exact hsame_trans dropZero (natModFn_of_strict nUnary nNonempty xUnary x.isLt)

theorem zmodZero_add_right {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x : ZMod n) :
    zmodEq (zmodAdd n nUnary nNonempty x (zmodZero n nUnary nNonempty)) x := by
  exact zmodEq_trans (zmodAdd_comm nUnary nNonempty x (zmodZero n nUnary nNonempty))
    (zmodZero_add_left nUnary nNonempty x)

theorem zmodAdd_neg_left {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x : ZMod n) :
    zmodEq (zmodAdd n nUnary nNonempty (zmodNeg n nUnary nNonempty x) x)
      (zmodZero n nUnary nNonempty) := by
  change hsame (natModFn n (append (natComplementMod n x.val) x.val)) BHist.Empty
  exact natComplementMod_add_right_zero_of_strict nUnary nNonempty
    (zmodVal_unary nUnary x) x.isLt

theorem zmodAdd_neg_right {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x : ZMod n) :
    zmodEq (zmodAdd n nUnary nNonempty x (zmodNeg n nUnary nNonempty x))
      (zmodZero n nUnary nNonempty) := by
  exact zmodEq_trans (zmodAdd_comm nUnary nNonempty x (zmodNeg n nUnary nNonempty x))
    (zmodAdd_neg_left nUnary nNonempty x)

theorem zmodMul_comm {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x y : ZMod n) :
    zmodEq (zmodMul n nUnary nNonempty x y)
      (zmodMul n nUnary nNonempty y x) := by
  exact natModFn_hsame_arg_transport (M := n)
    (natMulFn_comm_hsame (zmodVal_unary nUnary x) (zmodVal_unary nUnary y))

theorem zmodMul_assoc {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x y z : ZMod n) :
    zmodEq (zmodMul n nUnary nNonempty (zmodMul n nUnary nNonempty x y) z)
      (zmodMul n nUnary nNonempty x (zmodMul n nUnary nNonempty y z)) := by
  change hsame
    (natModFn n (natMulFn (natModFn n (natMulFn x.val y.val)) z.val))
    (natModFn n (natMulFn x.val (natModFn n (natMulFn y.val z.val))))
  have xUnary : UnaryHistory x.val := zmodVal_unary nUnary x
  have yUnary : UnaryHistory y.val := zmodVal_unary nUnary y
  have zUnary : UnaryHistory z.val := zmodVal_unary nUnary z
  have xyUnary : UnaryHistory (natMulFn x.val y.val) :=
    natMulFn_unary xUnary yUnary
  have yzUnary : UnaryHistory (natMulFn y.val z.val) :=
    natMulFn_unary yUnary zUnary
  have leftToRaw :
      hsame
        (natModFn n (natMulFn (natModFn n (natMulFn x.val y.val)) z.val))
        (natModFn n (natMulFn (natMulFn x.val y.val) z.val)) :=
    natModFn_mul_left_reduce_same_mod nUnary nNonempty xyUnary zUnary
  have rawAssoc :
      hsame
        (natModFn n (natMulFn (natMulFn x.val y.val) z.val))
        (natModFn n (natMulFn x.val (natMulFn y.val z.val))) := by
    exact natModFn_hsame_arg_transport (M := n)
      (NatMul_assoc_hsame xUnary yUnary zUnary
        (natMulFn_rel xUnary yUnary)
        (natMulFn_rel xyUnary zUnary)
        (natMulFn_rel yUnary zUnary)
        (natMulFn_rel xUnary yzUnary))
  have rawToRight :
      hsame
        (natModFn n (natMulFn x.val (natMulFn y.val z.val)))
        (natModFn n (natMulFn x.val (natModFn n (natMulFn y.val z.val)))) := by
    exact hsame_symm
      (natModFn_mul_right_reduce_same_mod nUnary nNonempty xUnary yzUnary)
  exact hsame_trans leftToRaw (hsame_trans rawAssoc rawToRight)

theorem zmodOne_mul_left {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x : ZMod n) :
    zmodEq (zmodMul n nUnary nNonempty (zmodOne n nUnary nNonempty) x) x := by
  change hsame (natModFn n (natMulFn (natModFn n NatOne) x.val)) x.val
  have xUnary : UnaryHistory x.val := zmodVal_unary nUnary x
  have productReduce :
      hsame (natModFn n (natMulFn (natModFn n NatOne) x.val))
        (natModFn n (natMulFn NatOne x.val)) :=
    natModFn_mul_left_reduce_same_mod nUnary nNonempty
      (unary_e1_closed unary_empty) xUnary
  have productUnit :
      hsame (natModFn n (natMulFn NatOne x.val)) (natModFn n x.val) :=
    natModFn_hsame_arg_transport (M := n)
      (NatMul_unit_left_hsame xUnary
        (natMulFn_rel (unary_e1_closed unary_empty) xUnary))
  exact hsame_trans productReduce
    (hsame_trans productUnit (natModFn_of_strict nUnary nNonempty xUnary x.isLt))

theorem zmodOne_mul_right {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x : ZMod n) :
    zmodEq (zmodMul n nUnary nNonempty x (zmodOne n nUnary nNonempty)) x := by
  exact zmodEq_trans (zmodMul_comm nUnary nNonempty x (zmodOne n nUnary nNonempty))
    (zmodOne_mul_left nUnary nNonempty x)

theorem zmodMul_add_distrib_left {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x y z : ZMod n) :
    zmodEq (zmodMul n nUnary nNonempty x (zmodAdd n nUnary nNonempty y z))
      (zmodAdd n nUnary nNonempty
        (zmodMul n nUnary nNonempty x y) (zmodMul n nUnary nNonempty x z)) := by
  change hsame
    (natModFn n (natMulFn x.val (natModFn n (append y.val z.val))))
    (natModFn n
      (append (natModFn n (natMulFn x.val y.val))
        (natModFn n (natMulFn x.val z.val))))
  have xUnary : UnaryHistory x.val := zmodVal_unary nUnary x
  have yUnary : UnaryHistory y.val := zmodVal_unary nUnary y
  have zUnary : UnaryHistory z.val := zmodVal_unary nUnary z
  have yzUnary : UnaryHistory (append y.val z.val) :=
    unary_append_closed yUnary zUnary
  have xyUnary : UnaryHistory (natMulFn x.val y.val) :=
    natMulFn_unary xUnary yUnary
  have xzUnary : UnaryHistory (natMulFn x.val z.val) :=
    natMulFn_unary xUnary zUnary
  have leftToRaw :
      hsame (natModFn n (natMulFn x.val (natModFn n (append y.val z.val))))
        (natModFn n (natMulFn x.val (append y.val z.val))) :=
    natModFn_mul_right_reduce_same_mod nUnary nNonempty xUnary yzUnary
  have rawDistrib :
      hsame (natModFn n (natMulFn x.val (append y.val z.val)))
        (natModFn n (append (natMulFn x.val y.val) (natMulFn x.val z.val))) :=
    natModFn_mul_add_distrib nUnary nNonempty xUnary yUnary zUnary
  have rawToRight :
      hsame (natModFn n (append (natMulFn x.val y.val) (natMulFn x.val z.val)))
        (natModFn n
          (append (natModFn n (natMulFn x.val y.val))
            (natModFn n (natMulFn x.val z.val)))) :=
    mod_add_compat nUnary nNonempty xyUnary xzUnary
  exact hsame_trans leftToRaw (hsame_trans rawDistrib rawToRight)

theorem zmodMul_add_distrib_right {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x y z : ZMod n) :
    zmodEq (zmodMul n nUnary nNonempty (zmodAdd n nUnary nNonempty x y) z)
      (zmodAdd n nUnary nNonempty
        (zmodMul n nUnary nNonempty x z) (zmodMul n nUnary nNonempty y z)) := by
  change hsame
    (natModFn n (natMulFn (natModFn n (append x.val y.val)) z.val))
    (natModFn n
      (append (natModFn n (natMulFn x.val z.val))
        (natModFn n (natMulFn y.val z.val))))
  have xUnary : UnaryHistory x.val := zmodVal_unary nUnary x
  have yUnary : UnaryHistory y.val := zmodVal_unary nUnary y
  have zUnary : UnaryHistory z.val := zmodVal_unary nUnary z
  have xyRawUnary : UnaryHistory (append x.val y.val) :=
    unary_append_closed xUnary yUnary
  have xzUnary : UnaryHistory (natMulFn x.val z.val) :=
    natMulFn_unary xUnary zUnary
  have yzUnary : UnaryHistory (natMulFn y.val z.val) :=
    natMulFn_unary yUnary zUnary
  have leftToRaw :
      hsame (natModFn n (natMulFn (natModFn n (append x.val y.val)) z.val))
        (natModFn n (natMulFn (append x.val y.val) z.val)) :=
    natModFn_mul_left_reduce_same_mod nUnary nNonempty xyRawUnary zUnary
  have rawDistrib :
      hsame (natModFn n (natMulFn (append x.val y.val) z.val))
        (natModFn n (append (natMulFn x.val z.val) (natMulFn y.val z.val))) :=
    natModFn_hsame_arg_transport (M := n)
      (natMulFn_append_right_distrib_hsame xUnary yUnary zUnary)
  have rawToRight :
      hsame (natModFn n (append (natMulFn x.val z.val) (natMulFn y.val z.val)))
        (natModFn n
          (append (natModFn n (natMulFn x.val z.val))
            (natModFn n (natMulFn y.val z.val)))) :=
    mod_add_compat nUnary nNonempty xzUnary yzUnary
  exact hsame_trans leftToRaw (hsame_trans rawDistrib rawToRight)

structure ZModCommRingCore (n : BHist) where
  n_unary : UnaryHistory n
  n_nonempty : hsame n BHist.Empty -> False
  carrier : Type
  eqv : carrier -> carrier -> Prop
  eq_refl : ∀ x : carrier, eqv x x
  eq_symm : ∀ {x y : carrier}, eqv x y -> eqv y x
  eq_trans : ∀ {x y z : carrier}, eqv x y -> eqv y z -> eqv x z
  zero : carrier
  one : carrier
  add : carrier -> carrier -> carrier
  mul : carrier -> carrier -> carrier
  neg : carrier -> carrier
  add_respects : ∀ {x x' y y' : carrier}, eqv x x' -> eqv y y' ->
    eqv (add x y) (add x' y')
  mul_respects : ∀ {x x' y y' : carrier}, eqv x x' -> eqv y y' ->
    eqv (mul x y) (mul x' y')
  neg_respects : ∀ {x y : carrier}, eqv x y -> eqv (neg x) (neg y)
  add_comm : ∀ x y : carrier, eqv (add x y) (add y x)
  add_assoc : ∀ x y z : carrier, eqv (add (add x y) z) (add x (add y z))
  zero_add : ∀ x : carrier, eqv (add zero x) x
  add_zero : ∀ x : carrier, eqv (add x zero) x
  neg_add : ∀ x : carrier, eqv (add (neg x) x) zero
  add_neg : ∀ x : carrier, eqv (add x (neg x)) zero
  mul_comm : ∀ x y : carrier, eqv (mul x y) (mul y x)
  mul_assoc : ∀ x y z : carrier, eqv (mul (mul x y) z) (mul x (mul y z))
  one_mul : ∀ x : carrier, eqv (mul one x) x
  mul_one : ∀ x : carrier, eqv (mul x one) x
  left_distrib : ∀ x y z : carrier, eqv (mul x (add y z)) (add (mul x y) (mul x z))
  right_distrib : ∀ x y z : carrier, eqv (mul (add x y) z) (add (mul x z) (mul y z))

def zmodCommRingCore (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) : ZModCommRingCore n :=
  { n_unary := nUnary
    n_nonempty := nNonempty
    carrier := ZMod n
    eqv := zmodEq
    eq_refl := zmodEq_refl
    eq_symm := zmodEq_symm
    eq_trans := zmodEq_trans
    zero := zmodZero n nUnary nNonempty
    one := zmodOne n nUnary nNonempty
    add := zmodAdd n nUnary nNonempty
    mul := zmodMul n nUnary nNonempty
    neg := zmodNeg n nUnary nNonempty
    add_respects := zmodAdd_congr nUnary nNonempty
    mul_respects := zmodMul_congr nUnary nNonempty
    neg_respects := zmodNeg_congr nUnary nNonempty
    add_comm := zmodAdd_comm nUnary nNonempty
    add_assoc := zmodAdd_assoc nUnary nNonempty
    zero_add := zmodZero_add_left nUnary nNonempty
    add_zero := zmodZero_add_right nUnary nNonempty
    neg_add := zmodAdd_neg_left nUnary nNonempty
    add_neg := zmodAdd_neg_right nUnary nNonempty
    mul_comm := zmodMul_comm nUnary nNonempty
    mul_assoc := zmodMul_assoc nUnary nNonempty
    one_mul := zmodOne_mul_left nUnary nNonempty
    mul_one := zmodOne_mul_right nUnary nNonempty
    left_distrib := zmodMul_add_distrib_left nUnary nNonempty
    right_distrib := zmodMul_add_distrib_right nUnary nNonempty }

end BEDC.Derived.ZModUp
