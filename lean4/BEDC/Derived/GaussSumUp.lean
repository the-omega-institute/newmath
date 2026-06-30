import BEDC.Algebra.FiniteFold
import BEDC.Derived.FermatWilsonUp
import BEDC.Derived.LegendreUp
import BEDC.Derived.QuadraticReciprocityComplete
import BEDC.Derived.ZModResidueList

namespace BEDC.Derived.GaussSumUp

open BEDC.Algebra.FiniteFold
open BEDC.Algebra.Rel
open BEDC.FKernel.Hist
open BEDC.Derived.FermatWilsonUp
open BEDC.Derived.LegendreUp
open BEDC.Derived.LegendreSymbolBridge
open BEDC.Derived.PrimeUp
open BEDC.Derived.QuadraticReciprocityComplete
open BEDC.Derived.QuadraticReciprocityUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.ZModResidueList
open BEDC.Derived.ZModUp

variable {A : Type u} {r : A -> A -> Prop}

/-- 一个有限循环相位系统；`rootPower a n` 表示 `zeta_p ^ (a*n)` 的承载项。 -/
structure CyclicPhase (p : BHist) (A : Type u) where
  rootPower : ZMod p -> ZMod p -> A

/-- Legendre 权重只以已有的关系分类出现，不把未闭合的平方类分解伪造成函数。 -/
def legendreWeight {p : BHist} (prime : NatPrime p) (n : ZMod p)
    (s : BEDC.Algebra.Rel.IntegerUp) : Prop :=
  legendreSym prime n s

/-- Gauss 求和的一项：把 Legendre 符号的整数值和循环相位相乘。 -/
def gaussTerm {p : BHist} (R : RelCommRing A r)
    (scale : BEDC.Algebra.Rel.IntegerUp -> A) (phase : CyclicPhase p A)
    (a n : ZMod p) (s : BEDC.Algebra.Rel.IntegerUp) : A :=
  R.mul (scale s) (phase.rootPower a n)

/-- 二次 Gauss 和的有限求和 carrier。调用方给出每个 residue 的 Legendre 分类值。 -/
def gaussSum {p : BHist} (prime : NatPrime p) (R : RelCommRing A r)
    (scale : BEDC.Algebra.Rel.IntegerUp -> A) (phase : CyclicPhase p A)
    (a : ZMod p) (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp) : A :=
  listSum R
    (List.map
      (fun n : ZMod p => gaussTerm R scale phase a n (symbol n))
      (nonzeroResidues prime))

def quadraticGaussSum {p : BHist} (prime : NatPrime p) (R : RelCommRing A r)
    (scale : BEDC.Algebra.Rel.IntegerUp -> A) (phase : CyclicPhase p A)
    (a : ZMod p) (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp) : A :=
  gaussSum prime R scale phase a symbol

def quadraticGaussProductTerm {p : BHist} (R : RelCommRing A r)
    (scale : BEDC.Algebra.Rel.IntegerUp -> A) (phase : CyclicPhase p A)
    (a b m n : ZMod p)
    (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp) : A :=
  R.mul
    (gaussTerm R scale phase a m (symbol m))
    (gaussTerm R scale phase b n (symbol n))

def quadraticGaussProductExpansion {p : BHist} (prime : NatPrime p)
    (R : RelCommRing A r) (scale : BEDC.Algebra.Rel.IntegerUp -> A)
    (phase : CyclicPhase p A) (a b : ZMod p)
    (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp) : A :=
  listSum R
    (List.map
      (fun m : ZMod p =>
        listSum R
          (List.map
            (fun n : ZMod p =>
              quadraticGaussProductTerm R scale phase a b m n symbol)
            (nonzeroResidues prime)))
      (nonzeroResidues prime))

def symbolClassifies {p : BHist} (prime : NatPrime p)
    (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp) : Prop :=
  ∀ n : ZMod p, n ∈ nonzeroResidues prime ->
    legendreSym prime n (symbol n)

def symbolMultiplicativeAlongUnit {p : BHist} (prime : NatPrime p)
    (u : ZMod p) (uNonzero : zmodNonzero u)
    (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp) : Prop :=
  ∀ n : ZMod p, n ∈ nonzeroResidues prime ->
    BEDC.Algebra.Rel.IntEq
      (symbol (zmodUnitMul prime u uNonzero n))
      (BEDC.Algebra.Rel.IntMul (symbol u) (symbol n))

def scaleRespects {A : Type u} {r : A -> A -> Prop} (_R : RelCommRing A r)
    (scale : BEDC.Algebra.Rel.IntegerUp -> A) : Prop :=
  ∀ {x y : BEDC.Algebra.Rel.IntegerUp},
    BEDC.Algebra.Rel.IntEq x y -> r (scale x) (scale y)

def scaleMulRespects {A : Type u} {r : A -> A -> Prop} (R : RelCommRing A r)
    (scale : BEDC.Algebra.Rel.IntegerUp -> A) : Prop :=
  ∀ x y : BEDC.Algebra.Rel.IntegerUp,
    r (scale (BEDC.Algebra.Rel.IntMul x y))
      (R.mul (scale x) (scale y))

def phaseUnitTransport {p : BHist} {A : Type u} {r : A -> A -> Prop}
    (prime : NatPrime p) (_R : RelCommRing A r) (phase : CyclicPhase p A)
    (a u : ZMod p) (uNonzero : zmodNonzero u) : Prop :=
  ∀ n : ZMod p, n ∈ nonzeroResidues prime ->
    r (phase.rootPower a (zmodUnitMul prime u uNonzero n))
      (phase.rootPower
        (zmodOne p prime.left (NatPrime_empty_absurd prime))
        n)

theorem gaussTerm_respects_symbol {p : BHist} (R : RelCommRing A r)
    (scale : BEDC.Algebra.Rel.IntegerUp -> A) (phase : CyclicPhase p A)
    (scale_ok : scaleRespects R scale) (a n : ZMod p)
    {s t : BEDC.Algebra.Rel.IntegerUp} :
    BEDC.Algebra.Rel.IntEq s t ->
      r (gaussTerm R scale phase a n s)
        (gaussTerm R scale phase a n t) := by
  intro same
  exact R.mul_congr (scale_ok same) (R.refl (phase.rootPower a n))

theorem listSum_map_mem (R : RelCommRing A r) {B : Type v}
    (f g : B -> A) :
    ∀ xs : List B, (∀ x : B, x ∈ xs -> r (f x) (g x)) ->
      r (listSum R (List.map f xs)) (listSum R (List.map g xs))
  | [], _same =>
      R.refl R.zero
  | x :: xs, same => by
      have headSame : r (f x) (g x) :=
        same x (List.Mem.head xs)
      have tailSame : r (listSum R (List.map f xs))
          (listSum R (List.map g xs)) :=
        listSum_map_mem R f g xs
          (fun y yMem => same y (List.Mem.tail x yMem))
      exact R.add_congr headSame tailSame

theorem list_map_comp_eq {B : Type v} {C : Type w} {D : Type x}
    (f : B -> C) (g : C -> D) :
    ∀ xs : List B, List.map g (List.map f xs) =
      List.map (fun x : B => g (f x)) xs
  | [] =>
      rfl
  | x :: xs =>
      congrArg (List.cons (g (f x))) (list_map_comp_eq f g xs)

theorem listSum_mul_left_map (R : RelCommRing A r) (x : A) {B : Type v}
    (f : B -> A) :
    ∀ xs : List B,
      r (R.mul x (listSum R (List.map f xs)))
        (listSum R (List.map (fun y : B => R.mul x (f y)) xs))
  | [] =>
      R.mul_zero x
  | y :: ys => by
      have tail := listSum_mul_left_map R x f ys
      exact R.trans
        (R.left_distrib x (f y) (listSum R (List.map f ys)))
        (R.add_congr (R.refl _) tail)

theorem listSum_mul_right_map (R : RelCommRing A r) (y : A) {B : Type v}
    (f : B -> A) :
    ∀ xs : List B,
      r (R.mul (listSum R (List.map f xs)) y)
        (listSum R (List.map (fun x : B => R.mul (f x) y) xs))
  | [] =>
      R.zero_mul y
  | x :: xs => by
      have tail := listSum_mul_right_map R y f xs
      exact R.trans
        (R.right_distrib (f x) (listSum R (List.map f xs)) y)
        (R.add_congr (R.refl _) tail)

theorem listSum_mul_listSum_map (R : RelCommRing A r) {B : Type v}
    {C : Type w} (f : B -> A) (g : C -> A) :
    ∀ xs : List B, ∀ ys : List C,
      r
        (R.mul (listSum R (List.map f xs))
          (listSum R (List.map g ys)))
        (listSum R
          (List.map
            (fun x : B =>
              listSum R
                (List.map (fun y : C => R.mul (f x) (g y)) ys))
            xs))
  | [], _ys =>
      R.zero_mul (listSum R (List.map g _ys))
  | x :: xs, ys => by
      have head :=
        listSum_mul_left_map R (f x) g ys
      have tail :=
        listSum_mul_listSum_map R f g xs ys
      exact R.trans
        (R.right_distrib (f x) (listSum R (List.map f xs))
          (listSum R (List.map g ys)))
        (R.add_congr head tail)

theorem quadraticGaussSum_product_expansion {p : BHist}
    (prime : NatPrime p) (R : RelCommRing A r)
    (scale : BEDC.Algebra.Rel.IntegerUp -> A) (phase : CyclicPhase p A)
    (a b : ZMod p) (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp) :
    r
      (R.mul
        (quadraticGaussSum prime R scale phase a symbol)
        (quadraticGaussSum prime R scale phase b symbol))
      (quadraticGaussProductExpansion prime R scale phase a b symbol) := by
  unfold quadraticGaussSum gaussSum quadraticGaussProductExpansion
    quadraticGaussProductTerm
  exact listSum_mul_listSum_map R
    (fun m : ZMod p => gaussTerm R scale phase a m (symbol m))
    (fun n : ZMod p => gaussTerm R scale phase b n (symbol n))
    (nonzeroResidues prime)
    (nonzeroResidues prime)

def quadraticGaussSquareFormula {p : BHist} (prime : NatPrime p)
    (R : RelCommRing A r) (scale : BEDC.Algebra.Rel.IntegerUp -> A)
    (phase : CyclicPhase p A) (a : ZMod p)
    (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp) : Prop :=
  r
    (R.mul
      (quadraticGaussSum prime R scale phase a symbol)
      (quadraticGaussSum prime R scale phase a symbol))
    (quadraticGaussProductExpansion prime R scale phase a a symbol)

theorem quadraticGaussSum_square_expansion {p : BHist}
    (prime : NatPrime p) (R : RelCommRing A r)
    (scale : BEDC.Algebra.Rel.IntegerUp -> A) (phase : CyclicPhase p A)
    (a : ZMod p) (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp) :
    quadraticGaussSquareFormula prime R scale phase a symbol := by
  unfold quadraticGaussSquareFormula
  exact quadraticGaussSum_product_expansion prime R scale phase a a symbol

def quadraticGaussPrimeSign (p : BHist) : QRSign :=
  minusOnePow
    (halfIndex (BEDC.FKernel.ExternalBinary.bwordLength p))

def quadraticGaussSquareSignedPrimeFormula {p : BHist} (prime : NatPrime p)
    (R : RelCommRing A r) (scale : BEDC.Algebra.Rel.IntegerUp -> A)
    (phase : CyclicPhase p A) (a : ZMod p)
    (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp)
    (signedPrimeScalar : QRSign -> BHist -> A) : Prop :=
  r
    (R.mul
      (quadraticGaussSum prime R scale phase a symbol)
      (quadraticGaussSum prime R scale phase a symbol))
    (signedPrimeScalar (quadraticGaussPrimeSign p) p)

theorem quadraticGaussSquareSignedPrimeFormula_from_expanded_evaluation
    {p : BHist} (prime : NatPrime p) (R : RelCommRing A r)
    (scale : BEDC.Algebra.Rel.IntegerUp -> A) (phase : CyclicPhase p A)
    (a : ZMod p) (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp)
    (signedPrimeScalar : QRSign -> BHist -> A) :
    r (quadraticGaussProductExpansion prime R scale phase a a symbol)
      (signedPrimeScalar (quadraticGaussPrimeSign p) p) ->
      quadraticGaussSquareSignedPrimeFormula prime R scale phase a symbol
        signedPrimeScalar := by
  intro expandedEvaluation
  unfold quadraticGaussSquareSignedPrimeFormula
  exact R.trans
    (quadraticGaussSum_square_expansion prime R scale phase a symbol)
    expandedEvaluation

def quadraticGaussNormSquareEqualsPrime {p : BHist} (prime : NatPrime p)
    (R : RelCommRing A r) (scale : BEDC.Algebra.Rel.IntegerUp -> A)
    (phase : CyclicPhase p A) (a : ZMod p)
    (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp)
    (normSq : A -> A) (primeScalar : BHist -> A) : Prop :=
  r (normSq (quadraticGaussSum prime R scale phase a symbol))
    (primeScalar p)

theorem quadraticGaussNormSquareFormula {p : BHist} (prime : NatPrime p)
    (R : RelCommRing A r) (scale : BEDC.Algebra.Rel.IntegerUp -> A)
    (phase : CyclicPhase p A) (a : ZMod p)
    (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp)
    (normSq conjugate : A -> A) (primeScalar : BHist -> A)
    (conjugateGauss : A) :
    (∀ x : A, r (normSq x) (R.mul x (conjugate x))) ->
      r (conjugate (quadraticGaussSum prime R scale phase a symbol))
        conjugateGauss ->
        r
          (R.mul
            (quadraticGaussSum prime R scale phase a symbol)
            conjugateGauss)
          (primeScalar p) ->
          quadraticGaussNormSquareEqualsPrime prime R scale phase a symbol
            normSq primeScalar := by
  intro normAsProduct conjugateEvaluation productEvaluation
  unfold quadraticGaussNormSquareEqualsPrime
  exact R.trans
    (normAsProduct (quadraticGaussSum prime R scale phase a symbol))
    (R.trans
      (R.mul_congr (R.refl _)
        conjugateEvaluation)
      productEvaluation)

theorem gaussSum_reindex_unit {p : BHist} (prime : NatPrime p)
    (R : RelCommRing A r) (scale : BEDC.Algebra.Rel.IntegerUp -> A)
    (phase : CyclicPhase p A) (a u : ZMod p) (uNonzero : zmodNonzero u)
    (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp) :
    r
      (listSum R
        (List.map
          (fun n : ZMod p =>
            gaussTerm R scale phase a
              (zmodUnitMul prime u uNonzero n)
              (symbol (zmodUnitMul prime u uNonzero n)))
          (nonzeroResidues prime)))
      (gaussSum prime R scale phase a symbol) := by
  unfold gaussSum
  have mapSame :
      List.map
        (fun n : ZMod p =>
          gaussTerm R scale phase a
            (zmodUnitMul prime u uNonzero n)
            (symbol (zmodUnitMul prime u uNonzero n)))
        (nonzeroResidues prime) =
      List.map
        (fun n : ZMod p =>
          gaussTerm R scale phase a n (symbol n))
        (List.map
          (fun n : ZMod p => zmodUnitMul prime u uNonzero n)
          (nonzeroResidues prime)) :=
    (list_map_comp_eq
      (fun n : ZMod p => zmodUnitMul prime u uNonzero n)
      (fun n : ZMod p => gaussTerm R scale phase a n (symbol n))
      (nonzeroResidues prime)).symm
  rw [mapSame]
  exact sum_permInvariant R
    (listPerm_map
      (fun n : ZMod p =>
        gaussTerm R scale phase a n (symbol n))
      (mulByUnit_permutes prime u uNonzero))

theorem gaussSum_unit_weight_relation {p : BHist} (prime : NatPrime p)
    (R : RelCommRing A r) (scale : BEDC.Algebra.Rel.IntegerUp -> A)
    (phase : CyclicPhase p A) (scale_ok : scaleRespects R scale)
    (a u : ZMod p) (uNonzero : zmodNonzero u)
    (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp)
    (symbol_mul : symbolMultiplicativeAlongUnit prime u uNonzero symbol) :
    r
      (listSum R
        (List.map
          (fun n : ZMod p =>
            gaussTerm R scale phase a
              (zmodUnitMul prime u uNonzero n)
              (symbol (zmodUnitMul prime u uNonzero n)))
          (nonzeroResidues prime)))
      (listSum R
        (List.map
          (fun n : ZMod p =>
            gaussTerm R scale phase a
              (zmodUnitMul prime u uNonzero n)
              (BEDC.Algebra.Rel.IntMul (symbol u) (symbol n)))
          (nonzeroResidues prime))) := by
  apply listSum_map_mem
  intro n nMem
  exact gaussTerm_respects_symbol R scale phase scale_ok a
    (zmodUnitMul prime u uNonzero n)
    (symbol_mul n nMem)

theorem gaussSum_unit_reindex_and_weight {p : BHist} (prime : NatPrime p)
    (R : RelCommRing A r) (scale : BEDC.Algebra.Rel.IntegerUp -> A)
    (phase : CyclicPhase p A) (scale_ok : scaleRespects R scale)
    (a u : ZMod p) (uNonzero : zmodNonzero u)
    (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp)
    (symbol_mul : symbolMultiplicativeAlongUnit prime u uNonzero symbol) :
    r (gaussSum prime R scale phase a symbol)
      (listSum R
        (List.map
          (fun n : ZMod p =>
            gaussTerm R scale phase a
              (zmodUnitMul prime u uNonzero n)
              (BEDC.Algebra.Rel.IntMul (symbol u) (symbol n)))
          (nonzeroResidues prime))) := by
  exact R.trans
    (R.symm (gaussSum_reindex_unit prime R scale phase a u uNonzero symbol))
    (gaussSum_unit_weight_relation prime R scale phase scale_ok
      a u uNonzero symbol symbol_mul)

theorem gaussSum_reindex_to_unit_phase {p : BHist} (prime : NatPrime p)
    (R : RelCommRing A r) (scale : BEDC.Algebra.Rel.IntegerUp -> A)
    (phase : CyclicPhase p A) (scale_ok : scaleRespects R scale)
    (a u : ZMod p) (uNonzero : zmodNonzero u)
    (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp)
    (symbol_mul : symbolMultiplicativeAlongUnit prime u uNonzero symbol)
    (phase_transport : phaseUnitTransport prime R phase a u uNonzero) :
    r (gaussSum prime R scale phase a symbol)
      (listSum R
        (List.map
          (fun n : ZMod p =>
            R.mul
              (scale (BEDC.Algebra.Rel.IntMul (symbol u) (symbol n)))
              (phase.rootPower
                (zmodOne p prime.left (NatPrime_empty_absurd prime))
                n))
          (nonzeroResidues prime))) := by
  exact R.trans
    (gaussSum_unit_reindex_and_weight prime R scale phase scale_ok
      a u uNonzero symbol symbol_mul)
    (by
      apply listSum_map_mem
      intro n nMem
      exact R.mul_congr (R.refl _)
        (phase_transport n nMem))

theorem listSum_const_mul_map (R : RelCommRing A r) (c : A) {B : Type v}
    (f : B -> A) :
    ∀ xs : List B,
      r (listSum R (List.map (fun x : B => R.mul c (f x)) xs))
        (R.mul c (listSum R (List.map f xs)))
  | [] =>
      R.symm (R.mul_zero c)
  | x :: xs => by
      have tail := listSum_const_mul_map R c f xs
      have step :
          r
            (R.add (R.mul c (f x))
              (listSum R (List.map (fun x : B => R.mul c (f x)) xs)))
            (R.add (R.mul c (f x))
              (R.mul c (listSum R (List.map f xs)))) :=
        R.add_congr (R.refl _) tail
      exact R.trans step
        (R.symm (R.left_distrib c (f x) (listSum R (List.map f xs))))

theorem gaussSum_unit_phase_factor_relation {p : BHist} (prime : NatPrime p)
    (R : RelCommRing A r) (scale : BEDC.Algebra.Rel.IntegerUp -> A)
    (phase : CyclicPhase p A) (scale_ok : scaleRespects R scale)
    (scale_mul : scaleMulRespects R scale)
    (a u : ZMod p) (uNonzero : zmodNonzero u)
    (symbol : ZMod p -> BEDC.Algebra.Rel.IntegerUp)
    (symbol_mul : symbolMultiplicativeAlongUnit prime u uNonzero symbol)
    (phase_transport : phaseUnitTransport prime R phase a u uNonzero)
    (symbol_unit_matches :
      BEDC.Algebra.Rel.IntEq (symbol u) (symbol a)) :
    r (gaussSum prime R scale phase a symbol)
      (R.mul (scale (symbol a))
        (gaussSum prime R scale phase
          (zmodOne p prime.left (NatPrime_empty_absurd prime))
          symbol)) := by
  let one := zmodOne p prime.left (NatPrime_empty_absurd prime)
  have transported :
      r (gaussSum prime R scale phase a symbol)
        (listSum R
          (List.map
            (fun n : ZMod p =>
              R.mul
                (scale (BEDC.Algebra.Rel.IntMul (symbol u) (symbol n)))
                (phase.rootPower one n))
            (nonzeroResidues prime))) :=
    gaussSum_reindex_to_unit_phase prime R scale phase scale_ok
      a u uNonzero symbol symbol_mul phase_transport
  have factoredTerms :
      r
        (listSum R
          (List.map
            (fun n : ZMod p =>
              R.mul
                (scale (BEDC.Algebra.Rel.IntMul (symbol u) (symbol n)))
                (phase.rootPower one n))
            (nonzeroResidues prime)))
        (listSum R
          (List.map
            (fun n : ZMod p =>
              R.mul (scale (symbol u))
                (gaussTerm R scale phase one n (symbol n)))
            (nonzeroResidues prime))) := by
    apply listSum_map_mem
    intro n _nMem
    exact R.trans
      (R.mul_congr (scale_mul (symbol u) (symbol n)) (R.refl _))
      (R.mul_assoc (scale (symbol u)) (scale (symbol n))
        (phase.rootPower one n))
  have factorOut :
      r
        (listSum R
          (List.map
            (fun n : ZMod p =>
              R.mul (scale (symbol u))
                (gaussTerm R scale phase one n (symbol n)))
            (nonzeroResidues prime)))
        (R.mul (scale (symbol u))
          (gaussSum prime R scale phase one symbol)) := by
    unfold gaussSum
    exact listSum_const_mul_map R (scale (symbol u))
      (fun n : ZMod p => gaussTerm R scale phase one n (symbol n))
      (nonzeroResidues prime)
  have symbolMove :
      r
        (R.mul (scale (symbol u))
          (gaussSum prime R scale phase one symbol))
        (R.mul (scale (symbol a))
          (gaussSum prime R scale phase one symbol)) :=
    R.mul_congr (scale_ok symbol_unit_matches) (R.refl _)
  exact R.trans transported
    (R.trans factoredTerms (R.trans factorOut symbolMove))

theorem gaussSum_quadratic_reciprocity_input_bridge
    {pHist qHist : BHist} {p q : Nat} {pq qp : QRSign} :
    VerifiedQuadraticReciprocityInputs pHist qHist p q pq qp ->
      QRFormulaEq p q pq qp := by
  intro inputs
  exact legendre_verified_inputs_quadratic_reciprocity_formula inputs

end BEDC.Derived.GaussSumUp
