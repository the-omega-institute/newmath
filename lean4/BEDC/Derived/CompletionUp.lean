import BEDC.Derived.MetricUp.PrefixIndependentSymmetric
import BEDC.Derived.MetricUp.Transport
import BEDC.Derived.RealUp

namespace BEDC.Derived.CompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.Cont
open BEDC.Derived.MetricUp
open BEDC.Derived.RealUp
open BEDC.Derived.RatUp

theorem CompletionMetricDistanceWitness_e1_tail_real_prefix_readback
    {x y : Nat -> BHist} {n : Nat} {tail : BHist} :
    RealStreamPrefixClassifier x y n -> MetricDistanceWitness (x n) (y n) (BHist.e1 tail) ->
      UnaryHistory tail ∧ RatHistoryClassifier (x n) (y n) := by
  intro hPrefix hDistance
  exact And.intro (unary_e1_inversion hDistance.2.2.1)
    (RealStreamPrefixClassifier_endpoint n hPrefix)

theorem CompletionMetricDistanceWitness_e1_tail_hsame_transport
    {x x' y y' : Nat -> BHist} {n : Nat} {tail : BHist}
    (sameX : forall m : Nat, hsame (x m) (x' m))
    (sameY : forall m : Nat, hsame (y m) (y' m)) :
    RealStreamPrefixClassifier x y n -> MetricDistanceWitness (x n) (y n) (BHist.e1 tail) ->
      RealStreamPrefixClassifier x' y' n ∧
        MetricDistanceWitness (x' n) (y' n) (BHist.e1 tail) ∧ UnaryHistory tail ∧
          RatHistoryClassifier (x' n) (y' n) := by
  intro hPrefix hDistance
  have hPrefix' : RealStreamPrefixClassifier x' y' n :=
    RealStreamPrefixClassifier_hsame_transport sameX sameY n hPrefix
  have distanceLedger' : Cont (x' n) (y' n) (BHist.e1 tail) :=
    MetricDistanceWitness_cont_hsame_transport (sameX n) (sameY n)
      (hsame_refl (BHist.e1 tail)) hDistance
  have hDistance' : MetricDistanceWitness (x' n) (y' n) (BHist.e1 tail) :=
    And.intro (unary_transport hDistance.left (sameX n))
      (And.intro (unary_transport hDistance.right.left (sameY n))
        (And.intro hDistance.right.right.left distanceLedger'))
  have readback :=
    CompletionMetricDistanceWitness_e1_tail_real_prefix_readback hPrefix' hDistance'
  exact And.intro hPrefix' (And.intro hDistance' readback)

theorem CompletionMetricDistanceWitness_e1_result_tail_deterministic
    {x y : Nat -> BHist} {n : Nat} {d e : BHist} :
    RealStreamPrefixClassifier x y n -> MetricDistanceWitness (x n) (y n) (BHist.e1 d) ->
      MetricDistanceWitness (x n) (y n) (BHist.e1 e) ->
        UnaryHistory d ∧ UnaryHistory e ∧ hsame d e ∧ RatHistoryClassifier (x n) (y n) := by
  intro hPrefix hDistanceD hDistanceE
  have dData :=
    CompletionMetricDistanceWitness_e1_tail_real_prefix_readback hPrefix hDistanceD
  have eData :=
    CompletionMetricDistanceWitness_e1_tail_real_prefix_readback hPrefix hDistanceE
  have sameDistance :
      hsame (BHist.e1 d) (BHist.e1 e) :=
    MetricDistanceWitness_hsame_result_deterministic
      (hsame_refl (x n)) (hsame_refl (y n)) hDistanceD hDistanceE
  exact And.intro dData.left
    (And.intro eData.left (And.intro (hsame_e1_iff.mp sameDistance) dData.right))

theorem CompletionMetricDistanceWitness_e1_symmetric_tail_real_prefix_readback
    {x y : Nat -> BHist} {n : Nat} {d e : BHist} :
    RealStreamPrefixClassifier x y n -> MetricDistanceWitness (x n) (y n) (BHist.e1 d) ->
      MetricDistanceWitness (y n) (x n) (BHist.e1 e) ->
        UnaryHistory d ∧ UnaryHistory e ∧ hsame d e ∧ RatHistoryClassifier (y n) (x n) := by
  intro hPrefix hDistanceD hDistanceE
  have hPrefixSymm : RealStreamPrefixClassifier y x n :=
    RealStreamPrefixClassifier_symm n hPrefix
  have dData :=
    CompletionMetricDistanceWitness_e1_tail_real_prefix_readback hPrefix hDistanceD
  have eData :=
    CompletionMetricDistanceWitness_e1_tail_real_prefix_readback hPrefixSymm hDistanceE
  have sameDistance :
      hsame (BHist.e1 d) (BHist.e1 e) :=
    MetricDistanceWitness_symmetric_classifier hDistanceD hDistanceE
  exact And.intro dData.left
    (And.intro eData.left (And.intro (hsame_e1_iff.mp sameDistance) eData.right))

theorem CompletionMetricDistanceWitness_visible_context_e1_tail_real_prefix_readback
    {x y : Nat -> BHist} {n : Nat} {p q tail : BHist} :
    RealStreamPrefixClassifier x y n ->
      MetricDistanceWitness (append p (x n)) (append (y n) q)
        (append (append p (BHist.e1 tail)) q) ->
        UnaryHistory tail ∧ RatHistoryClassifier (x n) (y n) := by
  intro hPrefix hDistance
  have visibleBase :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x n)
      (y := y n) (d := BHist.e1 tail)).mp hDistance
  exact And.intro (unary_e1_inversion visibleBase.right.right.right.right.left)
    (RealStreamPrefixClassifier_endpoint n hPrefix)

theorem CompletionMetricDistanceWitness_visible_context_empty_distance_real_prefix_readback
    {x y : Nat -> BHist} {n : Nat} {p q : BHist} :
    RealStreamPrefixClassifier x y n ->
      MetricDistanceWitness (append p (x n)) (append (y n) q)
        (append (append p BHist.Empty) q) ->
        UnaryHistory p ∧ UnaryHistory q ∧ hsame (x n) BHist.Empty ∧
          hsame (y n) BHist.Empty ∧ RatHistoryClassifier (x n) (y n) := by
  intro hPrefix hDistance
  have visibleBase :=
    (MetricDistanceWitness_visible_context_empty_distance_iff (p := p) (q := q)
      (x := x n) (y := y n)).mp hDistance
  exact And.intro visibleBase.left
    (And.intro visibleBase.right.left
      (And.intro visibleBase.right.right.left
        (And.intro visibleBase.right.right.right
          (RealStreamPrefixClassifier_endpoint n hPrefix))))

theorem CompletionMetricDistanceWitness_visible_context_empty_distance_hsame_transport
    {x x' y y' : Nat -> BHist} {n : Nat} {p q : BHist}
    (sameX : forall m : Nat, hsame (x m) (x' m))
    (sameY : forall m : Nat, hsame (y m) (y' m)) :
    RealStreamPrefixClassifier x y n ->
      MetricDistanceWitness (append p (x n)) (append (y n) q)
        (append (append p BHist.Empty) q) ->
        RealStreamPrefixClassifier x' y' n ∧
          MetricDistanceWitness (append p (x' n)) (append (y' n) q)
            (append (append p BHist.Empty) q) ∧
          UnaryHistory p ∧ UnaryHistory q ∧ hsame (x' n) BHist.Empty ∧
          hsame (y' n) BHist.Empty ∧ RatHistoryClassifier (x' n) (y' n) := by
  intro hPrefix hDistance
  have hPrefix' : RealStreamPrefixClassifier x' y' n :=
    RealStreamPrefixClassifier_hsame_transport sameX sameY n hPrefix
  have visibleBase :=
    (MetricDistanceWitness_visible_context_empty_distance_iff (p := p) (q := q)
      (x := x n) (y := y n)).mp hDistance
  have xEmpty' : hsame (x' n) BHist.Empty :=
    hsame_trans (hsame_symm (sameX n)) visibleBase.right.right.left
  have yEmpty' : hsame (y' n) BHist.Empty :=
    hsame_trans (hsame_symm (sameY n)) visibleBase.right.right.right
  have hDistance' :
      MetricDistanceWitness (append p (x' n)) (append (y' n) q)
        (append (append p BHist.Empty) q) :=
    (MetricDistanceWitness_visible_context_empty_distance_iff (p := p) (q := q)
      (x := x' n) (y := y' n)).mpr
      (And.intro visibleBase.left
        (And.intro visibleBase.right.left (And.intro xEmpty' yEmpty')))
  have ratClassifier' : RatHistoryClassifier (x' n) (y' n) :=
    RealStreamPrefixClassifier_endpoint n hPrefix'
  exact And.intro hPrefix'
    (And.intro hDistance'
      (And.intro visibleBase.left
        (And.intro visibleBase.right.left
          (And.intro xEmpty' (And.intro yEmpty' ratClassifier')))))

theorem CompletionMetricDistanceWitness_visible_context_e1_symmetric_tail_real_prefix_readback
    {x y : Nat -> BHist} {n : Nat} {p q d e : BHist} :
    RealStreamPrefixClassifier x y n ->
      MetricDistanceWitness (append p (x n)) (append (y n) q)
        (append (append p (BHist.e1 d)) q) ->
        MetricDistanceWitness (append p (y n)) (append (x n) q)
          (append (append p (BHist.e1 e)) q) ->
          UnaryHistory d ∧ UnaryHistory e ∧ hsame d e ∧ RatHistoryClassifier (y n) (x n) := by
  intro hPrefix hDistanceD hDistanceE
  have centralD :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x n)
      (y := y n) (d := BHist.e1 d)).mp hDistanceD
  have centralE :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := y n)
      (y := x n) (d := BHist.e1 e)).mp hDistanceE
  exact CompletionMetricDistanceWitness_e1_symmetric_tail_real_prefix_readback
    hPrefix centralD.right.right centralE.right.right

theorem CompletionMetricDistanceWitness_visible_context_e1_tail_deterministic
    {x y : Nat -> BHist} {n : Nat} {p q d e : BHist} :
    RealStreamPrefixClassifier x y n ->
      MetricDistanceWitness (append p (x n)) (append (y n) q)
        (append (append p (BHist.e1 d)) q) ->
      MetricDistanceWitness (append p (x n)) (append (y n) q)
        (append (append p (BHist.e1 e)) q) ->
        UnaryHistory d ∧ UnaryHistory e ∧ hsame d e ∧ RatHistoryClassifier (x n) (y n) := by
  intro hPrefix hDistanceD hDistanceE
  have dData :=
    CompletionMetricDistanceWitness_visible_context_e1_tail_real_prefix_readback
      hPrefix hDistanceD
  have eData :=
    CompletionMetricDistanceWitness_visible_context_e1_tail_real_prefix_readback
      hPrefix hDistanceE
  have sameVisibleTail : hsame (BHist.e1 d) (BHist.e1 e) :=
    MetricDistanceWitness_visible_context_result_deterministic hDistanceD hDistanceE
  exact And.intro dData.left
    (And.intro eData.left
      (And.intro (hsame_e1_iff.mp sameVisibleTail) dData.right))

theorem CompletionMetricDistanceWitness_visible_context_e1_prefix_independent_tail_deterministic
    {x y : Nat -> BHist} {n : Nat} {p q p' q' d e : BHist} :
    RealStreamPrefixClassifier x y n ->
      MetricDistanceWitness (append p (x n)) (append (y n) q)
        (append (append p (BHist.e1 d)) q) ->
      MetricDistanceWitness (append p' (x n)) (append (y n) q')
        (append (append p' (BHist.e1 e)) q') ->
        UnaryHistory d ∧ UnaryHistory e ∧ hsame d e ∧ RatHistoryClassifier (x n) (y n) := by
  intro hPrefix hDistanceD hDistanceE
  have dData :=
    CompletionMetricDistanceWitness_visible_context_e1_tail_real_prefix_readback
      hPrefix hDistanceD
  have eData :=
    CompletionMetricDistanceWitness_visible_context_e1_tail_real_prefix_readback
      hPrefix hDistanceE
  have sameVisibleTail : hsame (BHist.e1 d) (BHist.e1 e) :=
    MetricDistanceWitness_visible_context_prefix_independent_result_deterministic
      hDistanceD hDistanceE
  exact And.intro dData.left
    (And.intro eData.left
      (And.intro (hsame_e1_iff.mp sameVisibleTail) dData.right))

theorem CompletionMetricDistanceWitness_visible_context_e1_prefix_independent_symmetric_tail_readback
    {x y : Nat -> BHist} {n : Nat} {p q p' q' d e : BHist} :
    RealStreamPrefixClassifier x y n ->
      MetricDistanceWitness (append p (x n)) (append (y n) q)
        (append (append p (BHist.e1 d)) q) ->
      MetricDistanceWitness (append p' (y n)) (append (x n) q')
        (append (append p' (BHist.e1 e)) q') ->
        UnaryHistory d ∧ UnaryHistory e ∧ hsame d e ∧ RatHistoryClassifier (y n) (x n) := by
  intro hPrefix hDistanceD hDistanceE
  have hPrefixSymm : RealStreamPrefixClassifier y x n :=
    RealStreamPrefixClassifier_symm n hPrefix
  have dData :=
    CompletionMetricDistanceWitness_visible_context_e1_tail_real_prefix_readback
      hPrefix hDistanceD
  have eData :=
    CompletionMetricDistanceWitness_visible_context_e1_tail_real_prefix_readback
      hPrefixSymm hDistanceE
  have sameVisibleTail : hsame (BHist.e1 d) (BHist.e1 e) :=
    MetricDistanceWitness_visible_context_prefix_independent_symmetric_classifier
      hDistanceD hDistanceE
  exact And.intro dData.left
    (And.intro eData.left
      (And.intro (hsame_e1_iff.mp sameVisibleTail) eData.right))

end BEDC.Derived.CompletionUp
