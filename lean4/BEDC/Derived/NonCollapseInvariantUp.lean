import BEDC.Derived.LocatedReal.RatMetricKit
import BEDC.Derived.RHRoute.ZetaBoxEvaluator

namespace BEDC.Derived.NonCollapseInvariantUp

open BEDC.Derived.RationalUp
open BEDC.Derived.LocatedReal
open BEDC.Derived.IntUp
open BEDC.Derived.RHRoute.ZetaBoxEvaluator

structure SeparatingRatMetricKit (K : RatMetricKit) where
  apart_not_close :
    ∀ {x y : RatNum} {k : Nat}, K.apart x y k -> K.close x y k -> False

def EventualRatApart {K : RatMetricKit} (w : LReal K) (q : RatNum) : Prop :=
  ∃ k : Nat, ∀ bound : Nat, ∃ n : Nat, bound ≤ n ∧ K.apart (w.seq n) q k

def NonCollapseInvariant {K : RatMetricKit} (w : LReal K) : Prop :=
  ∀ q : RatNum, lrApart w (ratToLReal K q) ∧ EventualRatApart w q

structure NonCollapseWitness (K : RatMetricKit) where
  point : LReal K
  invariant : NonCollapseInvariant point

def BoxRatSeparated (box : ComplexBox) (q : RatNum) : Prop :=
  ratLt box.re.hi q ∨ ratLt q box.re.lo ∨
    ratLt box.im.hi ratZero ∨ ratLt ratZero box.im.lo

structure BoxStreamApart (G : BoxGauge) (w : BoxStream G) (q : RatNum) where
  precision : Nat
  fit_at_precision : G.fits (boxAt w precision) precision
  separated : BoxRatSeparated (boxAt w precision) q

def BoxStreamNonCollapseInvariant (G : BoxGauge) (w : BoxStream G) : Type :=
  ∀ q : RatNum, BoxStreamApart G w q

structure BoxStreamNonCollapseWitness where
  gauge : BoxGauge
  point : BoxStream gauge
  invariant : BoxStreamNonCollapseInvariant gauge point

theorem NonCollapseInvariant_lrApart {K : RatMetricKit} {w : LReal K}
    (h : NonCollapseInvariant w) (q : RatNum) :
    lrApart w (ratToLReal K q) :=
  (h q).left

theorem NonCollapseInvariant_eventual {K : RatMetricKit} {w : LReal K}
    (h : NonCollapseInvariant w) (q : RatNum) :
    EventualRatApart w q :=
  (h q).right

private theorem ratLt_not_RatEq {x y : RatNum} :
    ratLt x y -> RatEq x y -> False := by
  intro hlt same
  unfold ratLt intLtUp intLt at hlt
  unfold RatEq at same
  have lenEq := IntPairClassifier_length_eq same
  unfold IntMul ratDenInt at hlt
  rw [lenEq] at hlt
  exact Nat.lt_irrefl _ hlt

theorem ratExactApart_not_ratExactClose {x y : RatNum} {k : Nat} :
    ratExactApart x y k -> ratExactClose x y k -> False := by
  intro apart close
  cases apart with
  | inl xy =>
      exact ratLt_not_RatEq xy close
  | inr yx =>
      exact ratLt_not_RatEq yx (RatEq_symm close)

def RatMetricKitConcrete_separating :
    SeparatingRatMetricKit RatMetricKitConcrete where
  apart_not_close := by
    intro x y k apart close
    exact ratExactApart_not_ratExactClose (k := k) apart close

theorem NonCollapseInvariant_no_rat_retraction {K : RatMetricKit}
    (sep : SeparatingRatMetricKit K) {w : LReal K}
    (h : NonCollapseInvariant w) :
    ¬ ∃ q : RatNum, LRealEq K w (ratToLReal K q) := by
  intro retraction
  cases retraction with
  | intro q same =>
      cases same with
      | intro data =>
          have eventual := NonCollapseInvariant_eventual h q
          cases eventual with
          | intro k persists =>
              have apartAt := persists (data.modulus k)
              cases apartAt with
              | intro n apartData =>
              have close :
                  K.close (w.seq n) ((ratToLReal K q).seq (data.modulus k)) k :=
                data.close k n (data.modulus k) apartData.left
                  (Nat.le_refl (data.modulus k))
              change K.close (w.seq n) q k at close
              exact sep.apart_not_close apartData.right close

theorem NonCollapseWitness_no_rat_retraction {K : RatMetricKit}
    (sep : SeparatingRatMetricKit K) (witness : NonCollapseWitness K) :
    ¬ ∃ q : RatNum, LRealEq K witness.point (ratToLReal K q) :=
  NonCollapseInvariant_no_rat_retraction sep witness.invariant

theorem RatMetricKitConcrete_all_points_rat_retract
    (w : LReal RatMetricKitConcrete) :
    ∃ q : RatNum, LRealEq RatMetricKitConcrete w
      (ratToLReal RatMetricKitConcrete q) := by
  let q := w.seq (w.modulus 0)
  exact ⟨q,
    ⟨{
      modulus := fun _ => w.modulus 0
      close := by
        intro k m n hm _hn
        change RatEq (w.seq m) q
        exact w.cauchy 0 m (w.modulus 0) hm (Nat.le_refl (w.modulus 0))
    }⟩⟩

theorem RatMetricKitConcrete_no_noncollapse_witness :
    NonCollapseWitness RatMetricKitConcrete -> False := by
  intro witness
  exact
    NonCollapseWitness_no_rat_retraction RatMetricKitConcrete_separating witness
      (RatMetricKitConcrete_all_points_rat_retract witness.point)

end BEDC.Derived.NonCollapseInvariantUp
