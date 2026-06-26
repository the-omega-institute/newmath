import BEDC.Algebra.FiniteFold
import BEDC.Derived.ArithmeticFnUp
import BEDC.Derived.GcdUp
import BEDC.Derived.ZModUp

namespace BEDC.Derived.EulerTheoremUp

open BEDC.Algebra.Rel
open BEDC.Algebra.FiniteFold
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.GcdUp
open BEDC.Derived.IntUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModUp

variable {A : Type u} {r : A -> A -> Prop}

def relPow (R : RelCommRing A r) (a : A) : Nat -> A
  | 0 => R.one
  | k + 1 => R.mul (relPow R a k) a

def relUnit (R : RelCommRing A r) (x : A) : Prop :=
  ∃ y : A, r (R.mul x y) R.one ∧ r (R.mul y x) R.one

theorem relPow_succ (R : RelCommRing A r) (a : A) (k : Nat) :
    r (relPow R a (k + 1)) (R.mul (relPow R a k) a) := by
  exact R.refl (relPow R a (k + 1))

theorem listProd_left_mul
    (R : RelCommRing A r) (a : A) :
    ∀ xs : List A,
      r (listProd R (List.map (fun x : A => R.mul a x) xs))
        (R.mul (relPow R a xs.length) (listProd R xs))
  | [] => by
      exact R.symm (R.one_mul R.one)
  | x :: xs => by
      have tail := listProd_left_mul R a xs
      have start :
          r
            (R.mul (R.mul a x)
              (listProd R (List.map (fun x : A => R.mul a x) xs)))
            (R.mul (R.mul a x)
              (R.mul (relPow R a xs.length) (listProd R xs))) :=
        R.mul_congr (R.refl (R.mul a x)) tail
      have reassocOuter :
          r
            (R.mul (R.mul a x)
              (R.mul (relPow R a xs.length) (listProd R xs)))
            (R.mul a
              (R.mul x (R.mul (relPow R a xs.length) (listProd R xs)))) := by
        exact R.mul_assoc a x (R.mul (relPow R a xs.length) (listProd R xs))
      have movePow :
          r
            (R.mul a
              (R.mul x (R.mul (relPow R a xs.length) (listProd R xs))))
            (R.mul a
              (R.mul (relPow R a xs.length) (R.mul x (listProd R xs)))) := by
        exact R.mul_congr (R.refl a)
          (R.trans (R.symm
              (R.mul_assoc x (relPow R a xs.length) (listProd R xs)))
            (R.trans
              (R.mul_congr (R.mul_comm x (relPow R a xs.length))
                (R.refl (listProd R xs)))
              (R.mul_assoc (relPow R a xs.length) x (listProd R xs))))
      have reassocHead :
          r
            (R.mul a
              (R.mul (relPow R a xs.length) (R.mul x (listProd R xs))))
            (R.mul (R.mul a (relPow R a xs.length))
              (R.mul x (listProd R xs))) :=
        R.symm (R.mul_assoc a (relPow R a xs.length) (R.mul x (listProd R xs)))
      have commutePow :
          r
            (R.mul (R.mul a (relPow R a xs.length))
              (R.mul x (listProd R xs)))
            (R.mul (R.mul (relPow R a xs.length) a)
              (R.mul x (listProd R xs))) :=
        R.mul_congr (R.mul_comm a (relPow R a xs.length))
          (R.refl (R.mul x (listProd R xs)))
      exact R.trans start
        (R.trans reassocOuter
          (R.trans movePow
            (R.trans reassocHead commutePow)))

theorem cancel_right_by_unit
    (R : RelCommRing A r) {x y u : A} :
    relUnit R u -> r (R.mul x u) (R.mul y u) -> r x y := by
  intro unit sameProduct
  cases unit with
  | intro inv data =>
      have multiplied :
          r (R.mul (R.mul x u) inv) (R.mul (R.mul y u) inv) :=
        R.mul_congr sameProduct (R.refl inv)
      have leftReduce :
          r (R.mul (R.mul x u) inv) x := by
        exact R.trans (R.mul_assoc x u inv)
          (R.trans (R.mul_congr (R.refl x) data.left)
            (R.mul_one x))
      have rightReduce :
          r (R.mul (R.mul y u) inv) y := by
        exact R.trans (R.mul_assoc y u inv)
          (R.trans (R.mul_congr (R.refl y) data.left)
            (R.mul_one y))
      exact R.trans (R.symm leftReduce)
        (R.trans multiplied rightReduce)

theorem relUnit_one (R : RelCommRing A r) :
    relUnit R R.one := by
  exact ⟨R.one, R.mul_one R.one, R.one_mul R.one⟩

theorem relUnit_mul (R : RelCommRing A r) {x y : A} :
    relUnit R x -> relUnit R y -> relUnit R (R.mul x y) := by
  intro unitX unitY
  cases unitX with
  | intro invX invXData =>
      cases unitY with
      | intro invY invYData =>
          let inv := R.mul invY invX
          have leftReduce :
              r (R.mul (R.mul x y) inv) R.one := by
            have stepAssoc :
                r (R.mul (R.mul x y) inv)
                  (R.mul x (R.mul y inv)) :=
              R.mul_assoc x y inv
            have inner :
                r (R.mul y inv) invX := by
              exact R.trans (R.symm (R.mul_assoc y invY invX))
                (R.trans
                  (R.mul_congr invYData.left (R.refl invX))
                  (R.one_mul invX))
            have collapse :
                r (R.mul x (R.mul y inv)) (R.mul x invX) :=
              R.mul_congr (R.refl x) inner
            exact R.trans stepAssoc
              (R.trans collapse invXData.left)
          have rightReduce :
              r (R.mul inv (R.mul x y)) R.one := by
            exact R.trans (R.mul_comm inv (R.mul x y)) leftReduce
          exact ⟨inv, leftReduce, rightReduce⟩

theorem listProd_relUnit
    (R : RelCommRing A r) :
    ∀ xs : List A,
      (∀ x : A, x ∈ xs -> relUnit R x) ->
        relUnit R (listProd R xs)
  | [], _allUnits =>
      relUnit_one R
  | x :: xs, allUnits =>
      relUnit_mul R
        (allUnits x (List.Mem.head xs))
        (listProd_relUnit R xs
          (fun y mem => allUnits y (List.Mem.tail x mem)))

theorem euler_from_unit_product_permutation
    (R : RelCommRing A r) (a : A) (units : List A) :
    relUnit R (listProd R units) ->
      ListPerm (List.map (fun x : A => R.mul a x) units) units ->
        r (relPow R a units.length) R.one := by
  intro unitProduct perm
  have permProduct :
      r (listProd R (List.map (fun x : A => R.mul a x) units))
        (listProd R units) :=
    prod_permInvariant R perm
  have factorProduct :
      r (listProd R (List.map (fun x : A => R.mul a x) units))
        (R.mul (relPow R a units.length) (listProd R units)) :=
    listProd_left_mul R a units
  have sameProduct :
      r (R.mul (relPow R a units.length) (listProd R units))
        (R.mul R.one (listProd R units)) := by
    exact R.trans (R.symm factorProduct)
      (R.trans permProduct (R.symm (R.one_mul (listProd R units))))
  exact cancel_right_by_unit R unitProduct sameProduct

theorem euler_from_unit_list_permutation
    (R : RelCommRing A r) (a : A) (units : List A) :
    (∀ x : A, x ∈ units -> relUnit R x) ->
      ListPerm (List.map (fun x : A => R.mul a x) units) units ->
        r (relPow R a units.length) R.one := by
  intro allUnits perm
  exact euler_from_unit_product_permutation R a units
    (listProd_relUnit R units allUnits) perm

theorem zmodMul_zero_right {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (x : ZMod n) :
    zmodEq
      (zmodMul n nUnary nNonempty x
        (zmodZero n nUnary nNonempty))
      (zmodZero n nUnary nNonempty) := by
  change hsame (natModFn n (natMulFn x.val BHist.Empty)) BHist.Empty
  exact natModFn_of_strict nUnary nNonempty unary_empty
    (zmodZero n nUnary nNonempty).isLt

theorem zmodMul_zero_left {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (x : ZMod n) :
    zmodEq
      (zmodMul n nUnary nNonempty
        (zmodZero n nUnary nNonempty) x)
      (zmodZero n nUnary nNonempty) := by
  change hsame (natModFn n (natMulFn BHist.Empty x.val)) BHist.Empty
  have productZero :
      hsame (natMulFn BHist.Empty x.val) BHist.Empty :=
    NatMul_empty_left_result_empty
      (natMulFn_rel unary_empty (zmodVal_unary nUnary x))
  have modTransport :
      hsame (natModFn n (natMulFn BHist.Empty x.val))
        (natModFn n BHist.Empty) :=
    natModFn_hsame_arg_transport (M := n) productZero
  have modZero :
      hsame (natModFn n BHist.Empty) BHist.Empty :=
    natModFn_of_strict nUnary nNonempty unary_empty
      (zmodZero n nUnary nNonempty).isLt
  exact hsame_trans modTransport modZero

def zmodRelCommRing
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) :
    RelCommRing (ZMod n) zmodEq where
  zero := zmodZero n nUnary nNonempty
  one := zmodOne n nUnary nNonempty
  add := zmodAdd n nUnary nNonempty
  mul := zmodMul n nUnary nNonempty
  neg := zmodNeg n nUnary nNonempty
  refl := zmodEq_refl
  symm := zmodEq_symm
  trans := zmodEq_trans
  add_congr := zmodAdd_congr nUnary nNonempty
  mul_congr := zmodMul_congr nUnary nNonempty
  neg_congr := zmodNeg_congr nUnary nNonempty
  add_assoc := zmodAdd_assoc nUnary nNonempty
  add_comm := zmodAdd_comm nUnary nNonempty
  add_zero := zmodZero_add_right nUnary nNonempty
  zero_add := zmodZero_add_left nUnary nNonempty
  add_neg := zmodAdd_neg_right nUnary nNonempty
  neg_add := zmodAdd_neg_left nUnary nNonempty
  mul_assoc := zmodMul_assoc nUnary nNonempty
  mul_one := zmodOne_mul_right nUnary nNonempty
  one_mul := zmodOne_mul_left nUnary nNonempty
  mul_zero := zmodMul_zero_right nUnary nNonempty
  zero_mul := zmodMul_zero_left nUnary nNonempty
  left_distrib := zmodMul_add_distrib_left nUnary nNonempty
  right_distrib := zmodMul_add_distrib_right nUnary nNonempty
  mul_comm := zmodMul_comm nUnary nNonempty

def zmodPowByNat
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) (k : Nat) : ZMod n :=
  relPow (zmodRelCommRing n nUnary nNonempty) a k

theorem zmod_eulerPhi_from_unitPermutation
    {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (factors : List BHist)
    (a : ZMod n) (units : List (ZMod n)) :
    eulerPhiFactorsNat factors = units.length ->
      (∀ x : ZMod n, x ∈ units ->
        relUnit (zmodRelCommRing n nUnary nNonempty) x) ->
        ListPerm
          (List.map
            (fun x : ZMod n => zmodMul n nUnary nNonempty a x)
            units)
          units ->
          zmodEq
            (zmodPowByNat n nUnary nNonempty a
              (eulerPhiFactorsNat factors))
            (zmodOne n nUnary nNonempty) := by
  intro phiCount allUnits perm
  rw [phiCount]
  exact euler_from_unit_list_permutation
    (zmodRelCommRing n nUnary nNonempty) a units allUnits perm

end BEDC.Derived.EulerTheoremUp
