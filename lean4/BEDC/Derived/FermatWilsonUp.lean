import BEDC.Derived.ZModFieldUp
import BEDC.Derived.LegendreUp
import BEDC.Derived.FactorialUp
import BEDC.Derived.GcdUp
import BEDC.Algebra.FinPerm

namespace BEDC.Derived.FermatWilsonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp
open BEDC.Derived.ZModUp
open BEDC.Derived.ZModFieldUp
open BEDC.Algebra.Rel
open BEDC.Algebra.FiniteFold
open BEDC.Algebra.FinPerm

/-!
本文件导出 `ZMod p` 上通往 Fermat/Wilson 路线的乘法核心：
幂、非零幂、cancellation，以及非零剩余类左乘的显式逆映射。
-/

def zmodPow {p : BHist} (prime : NatPrime p) (x : ZMod p) : BHist -> ZMod p
  | BHist.Empty => zmodOne p prime.left (NatPrime_empty_absurd prime)
  | BHist.e0 _ => zmodOne p prime.left (NatPrime_empty_absurd prime)
  | BHist.e1 n =>
      zmodMul p prime.left (NatPrime_empty_absurd prime)
        (zmodPow prime x n) x

theorem zmodPow_empty {p : BHist} (prime : NatPrime p) (x : ZMod p) :
    zmodEq (zmodPow prime x BHist.Empty)
      (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
  rfl

theorem zmodPow_succ {p e : BHist} (prime : NatPrime p) (x : ZMod p) :
    zmodEq (zmodPow prime x (BHist.e1 e))
      (zmodMul p prime.left (NatPrime_empty_absurd prime)
        (zmodPow prime x e) x) := by
  rfl

theorem zmodPow_congr {p e : BHist} (prime : NatPrime p)
    {x y : ZMod p} :
    UnaryHistory e -> zmodEq x y ->
      zmodEq (zmodPow prime x e) (zmodPow prime y e) := by
  intro eUnary sameXY
  induction e with
  | Empty =>
      rfl
  | e0 eTail _ih =>
      cases eUnary
  | e1 eTail ih =>
      exact zmodMul_congr prime.left (NatPrime_empty_absurd prime)
        (ih (unary_e1_inversion eUnary)) sameXY

theorem zmodPow_nonzero {p e : BHist} (prime : NatPrime p)
    (x : ZMod p) :
    UnaryHistory e -> zmodNonzero x -> zmodNonzero (zmodPow prime x e) := by
  intro eUnary xNonzero
  induction e with
  | Empty =>
      exact zmodOne_nonzero prime
  | e0 eTail _ih =>
      cases eUnary
  | e1 eTail ih =>
      exact BEDC.Derived.LegendreUp.zmodMul_nonzero prime
        (ih (unary_e1_inversion eUnary)) xNonzero

theorem zmodMul_right_cancel_nonzero {p : BHist} (prime : NatPrime p)
    {a b c : ZMod p} :
    zmodNonzero c ->
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime) a c)
        (zmodMul p prime.left (NatPrime_empty_absurd prime) b c) ->
        zmodEq a b := by
  intro cNonzero sameProduct
  let mul := zmodMul p prime.left (NatPrime_empty_absurd prime)
  let invC := zmodInv prime c cNonzero
  have multiplied :
      zmodEq (mul (mul a c) invC) (mul (mul b c) invC) :=
    zmodMul_congr prime.left (NatPrime_empty_absurd prime)
      sameProduct (zmodEq_refl invC)
  have leftReduce : zmodEq (mul (mul a c) invC) a :=
    zmodEq_trans
      (zmodMul_assoc prime.left (NatPrime_empty_absurd prime) a c invC)
      (zmodEq_trans
        (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
          (zmodEq_refl a) (zmodInv_mul prime c cNonzero))
        (zmodOne_mul_right prime.left (NatPrime_empty_absurd prime) a))
  have rightReduce : zmodEq (mul (mul b c) invC) b :=
    zmodEq_trans
      (zmodMul_assoc prime.left (NatPrime_empty_absurd prime) b c invC)
      (zmodEq_trans
        (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
          (zmodEq_refl b) (zmodInv_mul prime c cNonzero))
        (zmodOne_mul_right prime.left (NatPrime_empty_absurd prime) b))
  exact zmodEq_trans (zmodEq_symm leftReduce)
    (zmodEq_trans multiplied rightReduce)

theorem zmodMul_left_cancel_nonzero {p : BHist} (prime : NatPrime p)
    {a b c : ZMod p} :
    zmodNonzero c ->
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime) c a)
        (zmodMul p prime.left (NatPrime_empty_absurd prime) c b) ->
        zmodEq a b := by
  intro cNonzero sameProduct
  let mul := zmodMul p prime.left (NatPrime_empty_absurd prime)
  have rightProduct : zmodEq (mul a c) (mul b c) :=
    zmodEq_trans
      (zmodMul_comm prime.left (NatPrime_empty_absurd prime) a c)
      (zmodEq_trans sameProduct
        (zmodEq_symm
          (zmodMul_comm prime.left (NatPrime_empty_absurd prime) b c)))
  exact zmodMul_right_cancel_nonzero prime cNonzero rightProduct

def zmodUnitMul {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (_aNonzero : zmodNonzero a) (x : ZMod p) : ZMod p :=
  zmodMul p prime.left (NatPrime_empty_absurd prime) a x

def zmodUnitDiv {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (aNonzero : zmodNonzero a) (x : ZMod p) : ZMod p :=
  zmodMul p prime.left (NatPrime_empty_absurd prime)
    (zmodInv prime a aNonzero) x

theorem zmodUnitDiv_unitMul {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (aNonzero : zmodNonzero a) (x : ZMod p) :
    zmodEq
      (zmodUnitDiv prime a aNonzero
        (zmodUnitMul prime a aNonzero x))
      x := by
  let mul := zmodMul p prime.left (NatPrime_empty_absurd prime)
  exact zmodEq_trans
    (zmodEq_symm
      (zmodMul_assoc prime.left (NatPrime_empty_absurd prime)
        (zmodInv prime a aNonzero) a x))
    (zmodEq_trans
      (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
        (zmodMul_inv prime a aNonzero) (zmodEq_refl x))
      (zmodOne_mul_left prime.left (NatPrime_empty_absurd prime) x))

theorem zmodUnitMul_unitDiv {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (aNonzero : zmodNonzero a) (x : ZMod p) :
    zmodEq
      (zmodUnitMul prime a aNonzero
        (zmodUnitDiv prime a aNonzero x))
      x := by
  let mul := zmodMul p prime.left (NatPrime_empty_absurd prime)
  exact zmodEq_trans
    (zmodEq_symm
      (zmodMul_assoc prime.left (NatPrime_empty_absurd prime)
        a (zmodInv prime a aNonzero) x))
    (zmodEq_trans
      (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
        (zmodInv_mul prime a aNonzero) (zmodEq_refl x))
      (zmodOne_mul_left prime.left (NatPrime_empty_absurd prime) x))

theorem zmodUnitMul_nonzero {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (aNonzero : zmodNonzero a) {x : ZMod p} :
    zmodNonzero x -> zmodNonzero (zmodUnitMul prime a aNonzero x) := by
  intro xNonzero
  exact BEDC.Derived.LegendreUp.zmodMul_nonzero prime aNonzero xNonzero

def zmodRelCommRing {p : BHist} (prime : NatPrime p) :
    RelCommRing (ZMod p) zmodEq where
  zero := zmodZero p prime.left (NatPrime_empty_absurd prime)
  one := zmodOne p prime.left (NatPrime_empty_absurd prime)
  add := zmodAdd p prime.left (NatPrime_empty_absurd prime)
  mul := zmodMul p prime.left (NatPrime_empty_absurd prime)
  neg := zmodNeg p prime.left (NatPrime_empty_absurd prime)
  refl := zmodEq_refl
  symm := zmodEq_symm
  trans := zmodEq_trans
  add_congr := zmodAdd_congr prime.left (NatPrime_empty_absurd prime)
  mul_congr := zmodMul_congr prime.left (NatPrime_empty_absurd prime)
  neg_congr := zmodNeg_congr prime.left (NatPrime_empty_absurd prime)
  add_assoc := zmodAdd_assoc prime.left (NatPrime_empty_absurd prime)
  add_comm := zmodAdd_comm prime.left (NatPrime_empty_absurd prime)
  add_zero := zmodZero_add_right prime.left (NatPrime_empty_absurd prime)
  zero_add := zmodZero_add_left prime.left (NatPrime_empty_absurd prime)
  add_neg := zmodAdd_neg_right prime.left (NatPrime_empty_absurd prime)
  neg_add := zmodAdd_neg_left prime.left (NatPrime_empty_absurd prime)
  mul_assoc := zmodMul_assoc prime.left (NatPrime_empty_absurd prime)
  mul_one := zmodOne_mul_right prime.left (NatPrime_empty_absurd prime)
  one_mul := zmodOne_mul_left prime.left (NatPrime_empty_absurd prime)
  mul_zero := by
    intro x
    change zmodEq
      (zmodMul p prime.left (NatPrime_empty_absurd prime) x
        (zmodZero p prime.left (NatPrime_empty_absurd prime)))
      (zmodZero p prime.left (NatPrime_empty_absurd prime))
    exact zmodEq_trans
      (zmodMul_comm prime.left (NatPrime_empty_absurd prime) x
        (zmodZero p prime.left (NatPrime_empty_absurd prime)))
      (zmodEq_trans
        (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
          (zmodEq_refl (zmodZero p prime.left (NatPrime_empty_absurd prime)))
          (zmodEq_refl x))
        (by
          change hsame
            (natModFn p (natMulFn BHist.Empty x.val)) BHist.Empty
          have xUnary : UnaryHistory x.val := zmodVal_unary prime.left x
          have rawZero : hsame (natMulFn BHist.Empty x.val) BHist.Empty :=
            NatMul_empty_left_result_empty (natMulFn_rel unary_empty xUnary)
          have modRaw :
              hsame
                (natModFn p (natMulFn BHist.Empty x.val))
                (natModFn p BHist.Empty) :=
            natModFn_hsame_arg_transport (M := p) rawZero
          exact hsame_trans modRaw
            (natModFn_of_strict prime.left (NatPrime_empty_absurd prime)
              unary_empty
              ⟨p, prime.left, NatPrime_empty_absurd prime, cont_left_unit p⟩)))
  zero_mul := by
    intro x
    change hsame (natModFn p (natMulFn BHist.Empty x.val)) BHist.Empty
    have xUnary : UnaryHistory x.val := zmodVal_unary prime.left x
    have rawZero : hsame (natMulFn BHist.Empty x.val) BHist.Empty :=
      NatMul_empty_left_result_empty (natMulFn_rel unary_empty xUnary)
    have modRaw :
        hsame
          (natModFn p (natMulFn BHist.Empty x.val))
          (natModFn p BHist.Empty) :=
      natModFn_hsame_arg_transport (M := p) rawZero
    exact hsame_trans modRaw
      (natModFn_of_strict prime.left (NatPrime_empty_absurd prime)
        unary_empty
        ⟨p, prime.left, NatPrime_empty_absurd prime, cont_left_unit p⟩)
  left_distrib := zmodMul_add_distrib_left prime.left (NatPrime_empty_absurd prime)
  right_distrib := zmodMul_add_distrib_right prime.left (NatPrime_empty_absurd prime)
  mul_comm := zmodMul_comm prime.left (NatPrime_empty_absurd prime)

def zmodPowNat {p : BHist} (prime : NatPrime p) (x : ZMod p) : Nat -> ZMod p
  | 0 => zmodOne p prime.left (NatPrime_empty_absurd prime)
  | n + 1 =>
      zmodMul p prime.left (NatPrime_empty_absurd prime)
        (zmodPowNat prime x n) x

theorem zmodPowNat_zero {p : BHist} (prime : NatPrime p) (x : ZMod p) :
    zmodEq (zmodPowNat prime x 0)
      (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
  rfl

theorem zmodPowNat_succ {p : BHist} (prime : NatPrime p) (x : ZMod p)
    (n : Nat) :
    zmodEq (zmodPowNat prime x (n + 1))
      (zmodMul p prime.left (NatPrime_empty_absurd prime)
        (zmodPowNat prime x n) x) := by
  rfl

theorem zmodPowNat_nonzero {p : BHist} (prime : NatPrime p)
    (x : ZMod p) :
    ∀ n : Nat, zmodNonzero x -> zmodNonzero (zmodPowNat prime x n)
  | 0, _xNonzero =>
      zmodOne_nonzero prime
  | n + 1, xNonzero =>
      BEDC.Derived.LegendreUp.zmodMul_nonzero prime
        (zmodPowNat_nonzero prime x n xNonzero) xNonzero

private theorem zmod_mul_four_shuffle {p : BHist} (prime : NatPrime p)
    (a x pow rest : ZMod p) :
    zmodEq
      (zmodMul p prime.left (NatPrime_empty_absurd prime)
        (zmodMul p prime.left (NatPrime_empty_absurd prime) a x)
        (zmodMul p prime.left (NatPrime_empty_absurd prime) pow rest))
      (zmodMul p prime.left (NatPrime_empty_absurd prime)
        (zmodMul p prime.left (NatPrime_empty_absurd prime) pow a)
        (zmodMul p prime.left (NatPrime_empty_absurd prime) x rest)) := by
  let R := zmodRelCommRing prime
  change zmodEq (R.mul (R.mul a x) (R.mul pow rest))
    (R.mul (R.mul pow a) (R.mul x rest))
  have first :
      zmodEq (R.mul (R.mul a x) (R.mul pow rest))
        (R.mul a (R.mul x (R.mul pow rest))) :=
    R.mul_assoc a x (R.mul pow rest)
  have inner :
      zmodEq (R.mul x (R.mul pow rest))
        (R.mul pow (R.mul x rest)) := by
    have stepA :
        zmodEq (R.mul x (R.mul pow rest))
          (R.mul (R.mul x pow) rest) :=
      R.symm (R.mul_assoc x pow rest)
    have stepB :
        zmodEq (R.mul (R.mul x pow) rest)
          (R.mul (R.mul pow x) rest) :=
      R.mul_congr (R.mul_comm x pow) (R.refl rest)
    have stepC :
        zmodEq (R.mul (R.mul pow x) rest)
          (R.mul pow (R.mul x rest)) :=
      R.mul_assoc pow x rest
    exact R.trans stepA (R.trans stepB stepC)
  have second :
      zmodEq (R.mul a (R.mul x (R.mul pow rest)))
        (R.mul a (R.mul pow (R.mul x rest))) :=
    R.mul_congr (R.refl a) inner
  have third :
      zmodEq (R.mul a (R.mul pow (R.mul x rest)))
        (R.mul (R.mul a pow) (R.mul x rest)) :=
    R.symm (R.mul_assoc a pow (R.mul x rest))
  have fourth :
      zmodEq (R.mul (R.mul a pow) (R.mul x rest))
        (R.mul (R.mul pow a) (R.mul x rest)) :=
    R.mul_congr (R.mul_comm a pow) (R.refl (R.mul x rest))
  exact R.trans first (R.trans second (R.trans third fourth))

theorem zmodUnitMul_listProd_expansion {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (aNonzero : zmodNonzero a) :
    ∀ xs : List (ZMod p),
      zmodEq
        (listProd (zmodRelCommRing prime)
          (List.map (zmodUnitMul prime a aNonzero) xs))
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          (zmodPowNat prime a xs.length)
          (listProd (zmodRelCommRing prime) xs))
  | [] => by
      change zmodEq
        (zmodOne p prime.left (NatPrime_empty_absurd prime))
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          (zmodOne p prime.left (NatPrime_empty_absurd prime))
          (zmodOne p prime.left (NatPrime_empty_absurd prime)))
      exact zmodEq_symm
        (zmodOne_mul_left prime.left (NatPrime_empty_absurd prime)
          (zmodOne p prime.left (NatPrime_empty_absurd prime)))
  | x :: xs => by
      let R := zmodRelCommRing prime
      have tail := zmodUnitMul_listProd_expansion prime a aNonzero xs
      have lift :
          zmodEq
            (R.mul (zmodUnitMul prime a aNonzero x)
              (listProd R (List.map (zmodUnitMul prime a aNonzero) xs)))
            (R.mul (zmodUnitMul prime a aNonzero x)
              (R.mul (zmodPowNat prime a xs.length) (listProd R xs))) :=
        R.mul_congr (R.refl (zmodUnitMul prime a aNonzero x)) tail
      have shuffle :
          zmodEq
            (R.mul (zmodUnitMul prime a aNonzero x)
              (R.mul (zmodPowNat prime a xs.length) (listProd R xs)))
            (R.mul (zmodPowNat prime a (List.length (x :: xs)))
              (R.mul x (listProd R xs))) := by
        change zmodEq
          (zmodMul p prime.left (NatPrime_empty_absurd prime)
            (zmodMul p prime.left (NatPrime_empty_absurd prime) a x)
            (zmodMul p prime.left (NatPrime_empty_absurd prime)
              (zmodPowNat prime a xs.length) (listProd R xs)))
          (zmodMul p prime.left (NatPrime_empty_absurd prime)
            (zmodMul p prime.left (NatPrime_empty_absurd prime)
              (zmodPowNat prime a xs.length) a)
            (zmodMul p prime.left (NatPrime_empty_absurd prime) x (listProd R xs)))
        exact zmod_mul_four_shuffle prime a x (zmodPowNat prime a xs.length)
          (listProd R xs)
      exact zmodEq_trans lift shuffle

theorem zmodListProd_nonzero {p : BHist} (prime : NatPrime p) :
    ∀ xs : List (ZMod p),
      (∀ x : ZMod p, x ∈ xs -> zmodNonzero x) ->
        zmodNonzero (listProd (zmodRelCommRing prime) xs)
  | [], _allNonzero =>
      zmodOne_nonzero prime
  | x :: xs, allNonzero => by
      have headNonzero : zmodNonzero x :=
        allNonzero x (List.Mem.head xs)
      have tailNonzero :
          zmodNonzero (listProd (zmodRelCommRing prime) xs) :=
        zmodListProd_nonzero prime xs
          (fun y member => allNonzero y (List.Mem.tail x member))
      exact BEDC.Derived.LegendreUp.zmodMul_nonzero prime
        headNonzero tailNonzero

theorem fermat_unit_list_permutation {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (aNonzero : zmodNonzero a) (xs : List (ZMod p)) :
    (∀ x : ZMod p, x ∈ xs -> zmodNonzero x) ->
      ListPerm (List.map (zmodUnitMul prime a aNonzero) xs) xs ->
        zmodEq (zmodPowNat prime a xs.length)
          (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
  intro allNonzero perm
  let R := zmodRelCommRing prime
  let prodXs := listProd R xs
  have prodNonzero : zmodNonzero prodXs :=
    zmodListProd_nonzero prime xs allNonzero
  have permProduct :
      zmodEq
        (listProd R (List.map (zmodUnitMul prime a aNonzero) xs))
        prodXs :=
    prod_permInvariant R perm
  have expanded :
      zmodEq
        (listProd R (List.map (zmodUnitMul prime a aNonzero) xs))
        (R.mul (zmodPowNat prime a xs.length) prodXs) :=
    zmodUnitMul_listProd_expansion prime a aNonzero xs
  have sameWithUnit :
      zmodEq
        (R.mul (zmodPowNat prime a xs.length) prodXs)
        (R.mul R.one prodXs) :=
    zmodEq_trans (zmodEq_symm expanded)
      (zmodEq_trans permProduct
        (zmodEq_symm
          (zmodOne_mul_left prime.left (NatPrime_empty_absurd prime) prodXs)))
  exact zmodMul_right_cancel_nonzero prime prodNonzero sameWithUnit

theorem fermat_unit_finperm {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (aNonzero : zmodNonzero a) {n : Nat}
    (f : Fin n -> ZMod p) (perm : FinPerm n) :
    (∀ x : ZMod p, x ∈ List.map f (finRange n) -> zmodNonzero x) ->
      ListPairwiseRel zmodEq
        (List.map (zmodUnitMul prime a aNonzero) (List.map f (finRange n)))
        (permutedValues perm f) ->
        zmodEq (zmodPowNat prime a (List.map f (finRange n)).length)
          (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
  intro allNonzero mulMatchesPerm
  let R := zmodRelCommRing prime
  let xs := List.map f (finRange n)
  have matchedProduct :
      zmodEq
        (listProd R (List.map (zmodUnitMul prime a aNonzero) xs))
        (listProd R (permutedValues perm f)) :=
    prod_congr R mulMatchesPerm
  have permProduct :
      zmodEq
        (listProd R (permutedValues perm f))
        (listProd R xs) :=
    listProd_finPermInvariant R perm f
  have mappedPerm :
      zmodEq
        (listProd R (List.map (zmodUnitMul prime a aNonzero) xs))
        (listProd R xs) :=
    zmodEq_trans matchedProduct permProduct
  have expanded :
      zmodEq
        (listProd R (List.map (zmodUnitMul prime a aNonzero) xs))
        (R.mul (zmodPowNat prime a xs.length) (listProd R xs)) :=
    zmodUnitMul_listProd_expansion prime a aNonzero xs
  have prodNonzero : zmodNonzero (listProd R xs) :=
    zmodListProd_nonzero prime xs allNonzero
  have sameWithUnit :
      zmodEq
        (R.mul (zmodPowNat prime a xs.length) (listProd R xs))
        (R.mul R.one (listProd R xs)) :=
    zmodEq_trans (zmodEq_symm expanded)
      (zmodEq_trans mappedPerm
        (zmodEq_symm
          (zmodOne_mul_left prime.left (NatPrime_empty_absurd prime)
            (listProd R xs))))
  exact zmodMul_right_cancel_nonzero prime prodNonzero sameWithUnit

end BEDC.Derived.FermatWilsonUp
