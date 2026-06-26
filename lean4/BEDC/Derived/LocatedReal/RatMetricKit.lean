import BEDC.Derived.LocatedReal
import BEDC.Derived.RationalUp.MetricOrder

namespace BEDC.Derived.LocatedReal

open BEDC.Derived.RationalUp

def ratExactClose (x y : Rat) (_k : Nat) : Prop :=
  RatEq x y

def ratExactApart (x y : Rat) (_k : Nat) : Prop :=
  ratLt x y ∨ ratLt y x

theorem ratExactClose_refl (x : Rat) (k : Nat) :
    ratExactClose x x k := by
  exact RatEq_refl x

theorem ratExactClose_symm {x y : Rat} {k : Nat} :
    ratExactClose x y k -> ratExactClose y x k := by
  intro h
  exact RatEq_symm h

theorem ratExactClose_weaken {x y : Rat} {hi lo : Nat} :
    lo ≤ hi -> ratExactClose x y hi -> ratExactClose x y lo := by
  intro _ h
  exact h

theorem ratExactClose_triangle {x y z : Rat} {k : Nat} :
    ratExactClose x y (Nat.succ k) ->
      ratExactClose y z (Nat.succ k) ->
        ratExactClose x z k := by
  intro xy yz
  exact RatEq_trans x y z xy yz

theorem ratExactClose_add {x x' y y' : Rat} {k : Nat} :
    ratExactClose x x' (Nat.succ k) ->
      ratExactClose y y' (Nat.succ k) ->
        ratExactClose (ratAdd x y) (ratAdd x' y') k := by
  intro xx' yy'
  exact ratAdd_respects xx' yy'

theorem ratExactClose_neg {x y : Rat} {k : Nat} :
    ratExactClose x y k -> ratExactClose (ratNeg x) (ratNeg y) k := by
  intro h
  exact ratNeg_respects h

theorem ratExactApart_symm {x y : Rat} {k : Nat} :
    ratExactApart x y k -> ratExactApart y x k := by
  intro h
  cases h with
  | inl xy => exact Or.inr xy
  | inr yx => exact Or.inl yx

def RatMetricKitConcrete : RatMetricKit where
  close := ratExactClose
  apart := ratExactApart
  le := RatEq
  close_refl := ratExactClose_refl
  close_symm := by
    intro x y k
    exact ratExactClose_symm
  close_weaken := by
    intro x y hi lo
    exact ratExactClose_weaken
  close_triangle := by
    intro x y z k
    exact ratExactClose_triangle
  eq_close := by
    intro x y h k
    exact h
  add_close := by
    intro x x' y y' k
    exact ratExactClose_add
  neg_close := by
    intro x y k
    exact ratExactClose_neg
  le_refl := RatEq_refl
  le_trans := by
    intro x y z xy yz
    exact RatEq_trans x y z xy yz
  le_antisymm := by
    intro x y xy _yx
    exact xy
  apart_symm := by
    intro x y k
    exact ratExactApart_symm

def concreteRatToLReal (q : Rat) : LReal RatMetricKitConcrete :=
  ratToLReal RatMetricKitConcrete q

theorem concreteRatToLReal_monotone {q r : Rat} :
    RatEq q r -> lrLe (concreteRatToLReal q) (concreteRatToLReal r) := by
  intro h n
  exact h

def concreteLrAdd (a b : LReal RatMetricKitConcrete) : LReal RatMetricKitConcrete :=
  lrAdd a b

def concreteLrLimit (s : Nat -> LReal RatMetricKitConcrete)
    (C : LRealSeqCauchy s) : LReal RatMetricKitConcrete :=
  lrLimit s C

def constantZeroLReal : LReal RatMetricKitConcrete :=
  concreteRatToLReal ratZero

def constantZeroSequence_cauchy :
    LRealSeqCauchy (fun _n : Nat => constantZeroLReal) := by
  exact {
    index := fun _ => 0
    index_mono := by
      intro i j hij
      exact Nat.le_refl 0
    cauchy := by
      intro k m n hm hn
      exact RatEq_refl ratZero
  }

def constantZeroLimit : LReal RatMetricKitConcrete :=
  lrLimit (fun _n : Nat => constantZeroLReal) constantZeroSequence_cauchy

theorem constantZeroLimit_cauchy :
    ∀ (k m n : Nat), constantZeroLimit.modulus k ≤ m ->
      constantZeroLimit.modulus k ≤ n ->
        RatMetricKitConcrete.close
          (constantZeroLimit.seq m) (constantZeroLimit.seq n) k :=
  constantZeroLimit.cauchy

end BEDC.Derived.LocatedReal
