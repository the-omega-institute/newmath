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

private theorem natLeBool_true_to_le_local {a b : Nat} :
    BEDC.Derived.IntUp.natLeBool a b = true -> a ≤ b := by
  induction a generalizing b with
  | zero =>
      intro _h
      exact Nat.zero_le b
  | succ a ih =>
      intro h
      cases b with
      | zero =>
          cases h
      | succ b =>
          exact Nat.succ_le_succ (ih h)

theorem ratLtBool_true_to_ratLt {x y : RatNum} :
    ratLtBool x y = true -> ratLt x y := by
  intro h
  unfold ratLtBool at h
  unfold ratLt intLtUp intLt
  exact Nat.lt_of_succ_le (natLeBool_true_to_le_local h)

theorem ratLt_to_ratLtBool {x y : RatNum} :
    ratLt x y -> ratLtBool x y = true := by
  intro h
  unfold ratLtBool
  unfold ratLt intLtUp intLt at h
  exact BEDC.Derived.IntUp.natLeBool_true_of_le (Nat.succ_le_of_lt h)

private theorem ratLt_not_RatEq_for_interval {x y : RatNum} :
    ratLt x y -> RatEq x y -> False := by
  intro hlt same
  unfold ratLt intLtUp intLt at hlt
  unfold RatEq at same
  have lenEq := IntPairClassifier_length_eq same
  unfold IntMul ratDenInt at hlt
  rw [lenEq] at hlt
  exact Nat.lt_irrefl _ hlt

def QIntervalRatIn (I : QInterval) (q : RatNum) : Prop :=
  ratLe I.lo q ∧ ratLe q I.hi

def QIntervalRatSeparated (I : QInterval) (q : RatNum) : Prop :=
  ratLt I.hi q ∨ ratLt q I.lo

def QIntervalRatSeparatedBool (I : QInterval) (q : RatNum) : Bool :=
  ratLtBool I.hi q || ratLtBool q I.lo

theorem QIntervalRatSeparatedBool_sound {I : QInterval} {q : RatNum} :
    QIntervalRatSeparatedBool I q = true -> QIntervalRatSeparated I q := by
  intro h
  unfold QIntervalRatSeparatedBool at h
  cases hiCase : ratLtBool I.hi q with
  | true =>
      exact Or.inl (ratLtBool_true_to_ratLt hiCase)
  | false =>
      rw [hiCase] at h
      exact Or.inr (ratLtBool_true_to_ratLt h)

theorem QIntervalRatSeparatedBool_complete {I : QInterval} {q : RatNum} :
    QIntervalRatSeparated I q -> QIntervalRatSeparatedBool I q = true := by
  intro h
  unfold QIntervalRatSeparatedBool
  cases h with
  | inl hi_lt =>
      rw [ratLt_to_ratLtBool hi_lt]
      rfl
  | inr lo_lt =>
      rw [ratLt_to_ratLtBool lo_lt]
      cases ratLtBool I.hi q <;> rfl

def ComplexBoxRatIn (box : ComplexBox) (q : RatNum) : Prop :=
  QIntervalRatIn box.re q ∧ QIntervalRatIn box.im ratZero

theorem QIntervalRatSeparated.not_in {I : QInterval} {q : RatNum} :
    QIntervalRatSeparated I q -> QIntervalRatIn I q -> False := by
  intro separated inside
  cases separated with
  | inl hi_lt_q =>
      exact ratLt_not_RatEq_for_interval hi_lt_q
        (ratLe_antisymm (ratLt_to_ratLe hi_lt_q) inside.right)
  | inr q_lt_lo =>
      exact ratLt_not_RatEq_for_interval q_lt_lo
        (ratLe_antisymm (ratLt_to_ratLe q_lt_lo) inside.left)

theorem BoxRatSeparated.not_in {box : ComplexBox} {q : RatNum} :
    BoxRatSeparated box q -> ComplexBoxRatIn box q -> False := by
  intro separated inside
  cases separated with
  | inl re_hi =>
      exact QIntervalRatSeparated.not_in (I := box.re) (q := q)
        (Or.inl re_hi) inside.left
  | inr rest =>
      cases rest with
      | inl re_lo =>
          exact QIntervalRatSeparated.not_in (I := box.re) (q := q)
            (Or.inr re_lo) inside.left
      | inr im_rest =>
          cases im_rest with
          | inl im_hi =>
              exact QIntervalRatSeparated.not_in (I := box.im) (q := ratZero)
                (Or.inl im_hi) inside.right
          | inr im_lo =>
              exact QIntervalRatSeparated.not_in (I := box.im) (q := ratZero)
                (Or.inr im_lo) inside.right

structure BoxStreamApart (G : BoxGauge) (w : BoxStream G) (q : RatNum) where
  precision : Nat
  fit_at_precision : G.fits (boxAt w precision) precision
  separated : BoxRatSeparated (boxAt w precision) q

def BoxStreamNonCollapseInvariant (G : BoxGauge) (w : BoxStream G) : Type :=
  ∀ q : RatNum, BoxStreamApart G w q

def BoxStreamRatRetraction (G : BoxGauge) (w : BoxStream G) (q : RatNum) : Prop :=
  ∀ precision : Nat, ComplexBoxRatIn (boxAt w precision) q

def BoxStreamExactRatRetraction (G : BoxGauge) (w : BoxStream G) : Prop :=
  ∃ q : RatNum, BoxStreamRatRetraction G w q

structure BoxStreamNonCollapseWitness where
  gauge : BoxGauge
  point : BoxStream gauge
  invariant : BoxStreamNonCollapseInvariant gauge point

theorem BoxStreamApart.no_rat_retraction {G : BoxGauge} {w : BoxStream G}
    {q : RatNum} :
    BoxStreamApart G w q -> BoxStreamRatRetraction G w q -> False := by
  intro apart retraction
  exact BoxRatSeparated.not_in apart.separated (retraction apart.precision)

theorem BoxStreamNonCollapseInvariant.no_rat_retraction {G : BoxGauge}
    {w : BoxStream G} :
    BoxStreamNonCollapseInvariant G w ->
      BoxStreamExactRatRetraction G w -> False := by
  intro invariant retraction
  cases retraction with
  | intro q exactRat =>
      exact BoxStreamApart.no_rat_retraction (invariant q) exactRat

theorem BoxStreamNonCollapseWitness.no_rat_retraction
    (witness : BoxStreamNonCollapseWitness) :
    BoxStreamExactRatRetraction witness.gauge witness.point -> False :=
  BoxStreamNonCollapseInvariant.no_rat_retraction witness.invariant

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
