import BEDC.Derived.ZModResidueList

namespace BEDC.Derived.ZModResidueList

open BEDC.Algebra.FiniteFold
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.FactorialUp
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModUp

def unaryPred : BHist -> BHist
  | BHist.Empty => BHist.Empty
  | BHist.e0 _ => BHist.Empty
  | BHist.e1 tail => tail

theorem unaryPred_unary {n : BHist} :
    UnaryHistory n -> UnaryHistory (unaryPred n) := by
  intro nUnary
  cases n with
  | Empty =>
      exact unary_empty
  | e0 _ =>
      cases nUnary
  | e1 _tail =>
      exact unary_e1_inversion nUnary

def residueRawListProduct : List BHist -> BHist
  | [] => BHist.e1 BHist.Empty
  | x :: xs => natMulFn x (residueRawListProduct xs)

theorem residueRawListProduct_unary {xs : List BHist} :
    (∀ x : BHist, x ∈ xs -> UnaryHistory x) ->
      UnaryHistory (residueRawListProduct xs) := by
  intro allUnary
  induction xs with
  | nil =>
      change UnaryHistory (BHist.e1 BHist.Empty)
      exact unary_e1_closed unary_empty
  | cons x xs ih =>
      exact natMulFn_unary
        (allUnary x (List.Mem.head xs))
        (ih (fun y yMem => allUnary y (List.Mem.tail x yMem)))

theorem positiveBelow_member_unary {p r : BHist} :
    UnaryHistory p -> r ∈ positiveBelow p -> UnaryHistory r := by
  intro pUnary mem
  cases p with
  | Empty =>
      cases mem
  | e0 _ =>
      cases pUnary
  | e1 tail =>
      change r ∈ positiveUpTo tail at mem
      exact positiveUpTo_member_unary (unary_e1_inversion pUnary) mem

theorem positiveBelow_raw_product_unary {p : BHist} :
    UnaryHistory p -> UnaryHistory (residueRawListProduct (positiveBelow p)) := by
  intro pUnary
  exact residueRawListProduct_unary
    (fun r mem => positiveBelow_member_unary pUnary mem)

theorem positiveUpTo_list_prod_eq_factorial {n : BHist} :
    UnaryHistory n ->
      hsame (residueRawListProduct (positiveUpTo n)) (natFactorialFn n) := by
  intro nUnary
  induction n with
  | Empty =>
      change hsame (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)
      rfl
  | e0 _ =>
      cases nUnary
  | e1 tail ih =>
      change hsame
        (natMulFn (BHist.e1 tail) (residueRawListProduct (positiveUpTo tail)))
        (natMulFn (BHist.e1 tail) (natFactorialFn tail))
      exact natMulFn_hsame_transport (hsame_refl (BHist.e1 tail)) (ih nUnary)

theorem positiveBelow_list_prod_eq_factorial {p : BHist} :
    UnaryHistory p ->
      hsame (residueRawListProduct (positiveBelow p))
        (natFactorialFn (unaryPred p)) := by
  intro pUnary
  cases p with
  | Empty =>
      change hsame (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)
      rfl
  | e0 _ =>
      cases pUnary
  | e1 tail =>
      exact positiveUpTo_list_prod_eq_factorial (unary_e1_inversion pUnary)

def nonzeroResiduesAscending {p : BHist} (prime : NatPrime p) : List (ZMod p) :=
  (nonzeroResidues prime).reverse

def zmodFactorialBelow {p : BHist} (prime : NatPrime p) : ZMod p :=
  zmodFromNat p prime.left (NatPrime_empty_absurd prime)
    (natFactorialFn (unaryPred p))
    (natFactorialFn_unary (unaryPred_unary prime.left))

theorem zmod_residueListFrom_prod_eq_raw_mod {p : BHist} (prime : NatPrime p) :
    ∀ (xs : List BHist)
      (bounded : ∀ r : BHist, r ∈ xs -> NatUnaryStrictPrefix r p)
      (allUnary : ∀ r : BHist, r ∈ xs -> UnaryHistory r),
        zmodEq
          (listProd (BEDC.Derived.FermatWilsonUp.zmodRelCommRing prime)
            (residueListFrom xs bounded))
          (zmodFromNat p prime.left (NatPrime_empty_absurd prime)
            (residueRawListProduct xs)
            (residueRawListProduct_unary allUnary))
  | [], _bounded, _allUnary => by
      change hsame (natModFn p (BHist.e1 BHist.Empty))
        (natModFn p (BHist.e1 BHist.Empty))
      rfl
  | r :: rs, bounded, allUnary => by
      let head : ZMod p :=
        { val := r
          isLt := bounded r (List.Mem.head rs) }
      let tailBounded : ∀ x : BHist, x ∈ rs -> NatUnaryStrictPrefix x p :=
        fun x mem => bounded x (List.Mem.tail r mem)
      let tailUnary : ∀ x : BHist, x ∈ rs -> UnaryHistory x :=
        fun x mem => allUnary x (List.Mem.tail r mem)
      have tailProduct :
          zmodEq
            (listProd (BEDC.Derived.FermatWilsonUp.zmodRelCommRing prime)
              (residueListFrom rs tailBounded))
            (zmodFromNat p prime.left (NatPrime_empty_absurd prime)
              (residueRawListProduct rs)
              (residueRawListProduct_unary tailUnary)) :=
        zmod_residueListFrom_prod_eq_raw_mod prime rs tailBounded tailUnary
      have liftedTail :
          zmodEq
            (zmodMul p prime.left (NatPrime_empty_absurd prime) head
              (listProd (BEDC.Derived.FermatWilsonUp.zmodRelCommRing prime)
                (residueListFrom rs tailBounded)))
            (zmodMul p prime.left (NatPrime_empty_absurd prime) head
              (zmodFromNat p prime.left (NatPrime_empty_absurd prime)
                (residueRawListProduct rs)
                (residueRawListProduct_unary tailUnary))) :=
        zmodMul_congr prime.left (NatPrime_empty_absurd prime)
          (zmodEq_refl head) tailProduct
      have rUnary : UnaryHistory r :=
        allUnary r (List.Mem.head rs)
      have rawTailUnary : UnaryHistory (residueRawListProduct rs) :=
        residueRawListProduct_unary tailUnary
      have reduceTail :
          zmodEq
            (zmodMul p prime.left (NatPrime_empty_absurd prime) head
              (zmodFromNat p prime.left (NatPrime_empty_absurd prime)
                (residueRawListProduct rs)
                (residueRawListProduct_unary tailUnary)))
            (zmodFromNat p prime.left (NatPrime_empty_absurd prime)
              (natMulFn r (residueRawListProduct rs))
              (natMulFn_unary rUnary rawTailUnary)) := by
        change hsame
          (natModFn p
            (natMulFn r (natModFn p (residueRawListProduct rs))))
          (natModFn p (natMulFn r (residueRawListProduct rs)))
        exact natModFn_mul_right_reduce_same_mod prime.left
          (NatPrime_empty_absurd prime) rUnary rawTailUnary
      exact zmodEq_trans liftedTail reduceTail

theorem nonzeroResidues_prod_eq_factorial_mod {p : BHist}
    (prime : NatPrime p) :
    zmodEq
      (listProd (BEDC.Derived.FermatWilsonUp.zmodRelCommRing prime)
        (nonzeroResidues prime))
      (zmodFactorialBelow prime) := by
  have productRaw :
      zmodEq
        (listProd (BEDC.Derived.FermatWilsonUp.zmodRelCommRing prime)
          (nonzeroResidues prime))
        (zmodFromNat p prime.left (NatPrime_empty_absurd prime)
          (residueRawListProduct (positiveBelow p))
          (positiveBelow_raw_product_unary prime.left)) := by
    unfold nonzeroResidues
    exact zmod_residueListFrom_prod_eq_raw_mod prime (positiveBelow p)
      (fun r rawMem => positiveBelow_member_lt prime.left rawMem)
      (fun r rawMem => positiveBelow_member_unary prime.left rawMem)
  have rawFactorial :
      hsame (residueRawListProduct (positiveBelow p))
        (natFactorialFn (unaryPred p)) :=
    positiveBelow_list_prod_eq_factorial prime.left
  have modFactorial :
      zmodEq
        (zmodFromNat p prime.left (NatPrime_empty_absurd prime)
          (residueRawListProduct (positiveBelow p))
          (positiveBelow_raw_product_unary prime.left))
        (zmodFactorialBelow prime) := by
    change hsame
      (natModFn p (residueRawListProduct (positiveBelow p)))
      (natModFn p (natFactorialFn (unaryPred p)))
    exact natModFn_hsame_arg_transport (M := p) rawFactorial
  exact zmodEq_trans productRaw modFactorial

theorem residue_list_prod_eq_factorial {p : BHist} (prime : NatPrime p) :
    zmodEq
      (listProd (BEDC.Derived.FermatWilsonUp.zmodRelCommRing prime)
        (nonzeroResiduesAscending prime))
      (zmodFactorialBelow prime) := by
  unfold nonzeroResiduesAscending
  exact zmodEq_trans
    (prod_reverse (BEDC.Derived.FermatWilsonUp.zmodRelCommRing prime)
      (nonzeroResidues prime))
    (nonzeroResidues_prod_eq_factorial_mod prime)

theorem zmod_nonzeroResidues_prod_eq_factorial_mod {p : BHist}
    (prime : NatPrime p) :
    zmodEq
      (listProd (BEDC.Derived.FermatWilsonUp.zmodRelCommRing prime)
        (nonzeroResidues prime))
      (zmodFactorialBelow prime) :=
  nonzeroResidues_prod_eq_factorial_mod prime

theorem zmod_nonzeroResiduesAscending_prod_eq_factorial_mod {p : BHist}
    (prime : NatPrime p) :
    zmodEq
      (listProd (BEDC.Derived.FermatWilsonUp.zmodRelCommRing prime)
        (nonzeroResiduesAscending prime))
      (zmodFactorialBelow prime) :=
  residue_list_prod_eq_factorial prime

end BEDC.Derived.ZModResidueList
