import BEDC.Algebra.FiniteFold
import BEDC.Derived.FermatWilsonUp
import BEDC.Derived.LegendreUp
import BEDC.Derived.ZModResidueList

namespace BEDC.Derived.GaussSumUp

open BEDC.Algebra.FiniteFold
open BEDC.Algebra.Rel
open BEDC.FKernel.Hist
open BEDC.Derived.FermatWilsonUp
open BEDC.Derived.LegendreUp
open BEDC.Derived.PrimeUp
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

end BEDC.Derived.GaussSumUp
