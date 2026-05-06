import BEDC.Derived.TopologyUp.Core

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem BHistFiniteBaseNeighborhood_append_decomposition
    (left right : ProbeBundle BHist) (ball : BHist -> BHist -> Prop) (x : BHist) :
    BHistFiniteBaseNeighborhood (bundleAppend left right) ball x <->
      BHistFiniteBaseNeighborhood left ball x ∧ BHistFiniteBaseNeighborhood right ball x := by
  constructor
  · intro appended
    constructor
    · intro i inLeft
      have inAppended : InBundle i (bundleAppend left right) :=
        Iff.mpr inBundle_bundleAppend_iff (Or.inl inLeft)
      exact appended i inAppended
    · intro i inRight
      have inAppended : InBundle i (bundleAppend left right) :=
        Iff.mpr inBundle_bundleAppend_iff (Or.inr inRight)
      exact appended i inAppended
  · intro split i inAppended
    have inEither : InBundle i left ∨ InBundle i right :=
      Iff.mp inBundle_bundleAppend_iff inAppended
    cases inEither with
    | inl inLeft =>
        exact split.left i inLeft
    | inr inRight =>
        exact split.right i inRight

def BHistFiniteBaseNeighborhoodCarrier (ball : BHist -> BHist -> Prop)
    (ballStable :
      forall {indices : ProbeBundle BHist} {i x y : BHist}, InBundle i indices ->
        UnaryHistory x -> UnaryHistory y -> hsame x y -> (ball i x <-> ball i y)) :
    BHistIndexedOpenCarrier := {
  OpenIx := ProbeBundle BHist
  OpenAt := fun indices x => BHistFiniteBaseNeighborhood indices ball x
  meet := fun left right => bundleAppend left right
  membership_stable := by
    intro indices x y unaryX unaryY sameXY
    exact
      BHistFiniteBaseNeighborhood_classifier_transport indices ball
        (by
          intro i x y inIndices unaryX unaryY sameXY
          exact ballStable (indices := indices) inIndices unaryX unaryY sameXY)
        unaryX unaryY sameXY
  meet_law := by
    intro left right x unaryX
    exact BHistFiniteBaseNeighborhood_append_decomposition left right ball x
}

theorem BHistFiniteBaseNeighborhoodCarrier_singleton_row (ball : BHist -> BHist -> Prop)
    (ballStable :
      forall {indices : ProbeBundle BHist} {i x y : BHist}, InBundle i indices ->
        UnaryHistory x -> UnaryHistory y -> hsame x y -> (ball i x <-> ball i y))
    {indices : ProbeBundle BHist} {ledger : BHist} (unaryLedger : UnaryHistory ledger) :
    BHistUnaryTopologyLedgerRow (BHistFiniteBaseNeighborhoodCarrier ball ballStable)
      indices (BHistFiniteBaseNeighborhood indices ball) := by
  apply BHistUnaryTopologyLedgerRow.singletonMetricBall ledger unaryLedger
  intro x unaryX
  constructor
  · intro neighborhood
    exact neighborhood
  · intro openNeighborhood
    exact openNeighborhood

theorem BHistFiniteBaseNeighborhoodCarrier_singleton_ball_carries (ball : BHist -> BHist -> Prop)
    (ballStable :
      forall {indices : ProbeBundle BHist} {i x y : BHist}, InBundle i indices ->
        UnaryHistory x -> UnaryHistory y -> hsame x y -> (ball i x <-> ball i y))
    (p ledger : BHist) (unaryLedger : UnaryHistory ledger) :
    BHistUnaryTopologyLedgerRow (BHistFiniteBaseNeighborhoodCarrier ball ballStable)
      (ProbeBundle.Bcons p ProbeBundle.Bnil) (fun x : BHist => ball p x) := by
  apply BHistUnaryTopologyLedgerRow.singletonMetricBall ledger unaryLedger
  intro x unaryX
  constructor
  · intro ballAt
    intro i inSingleton
    have iEqP : i = p := Iff.mp inBundle_singleton_iff inSingleton
    cases iEqP
    exact ballAt
  · intro neighborhood
    exact neighborhood p (inBundle_cons_self p ProbeBundle.Bnil)

structure BHistFiniteBaseNeighborhoodRow (T : BHistIndexedOpenCarrier)
    (indices : ProbeBundle BHist) (ball : BHist -> BHist -> Prop) (x : BHist) where
  point_unary : UnaryHistory x
  neighborhood : BHistFiniteBaseNeighborhood indices ball x
  index : T.OpenIx
  carries : BHistCarriesOpen T index (BHistFiniteBaseNeighborhood indices ball)
  ledger : BHist
  ledger_unary : UnaryHistory ledger
  row : BHistUnaryTopologyLedgerRow T index (BHistFiniteBaseNeighborhood indices ball)

end BEDC.Derived.TopologyUp
