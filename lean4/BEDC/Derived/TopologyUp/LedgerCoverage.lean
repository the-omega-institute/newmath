import BEDC.Derived.TopologyUp

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem BHistLedgerPublicOpenTree_constructor_exhaustion (T : BHistIndexedOpenCarrier)
    {i : T.OpenIx} {U : BHist -> Prop} {ledger : BHist} :
    BHistLedgerPublicOpenTree T i U ledger ->
      (BHistCarriesOpen T i U ∧ hsame ledger ledger) ∨
        (exists leftLedger : BHist, exists rightLedger : BHist,
          hsame ledger (BHist.e0 (append leftLedger rightLedger))) ∨
          hsame ledger (BHist.e1 BHist.Empty) ∨
            hsame ledger (BHist.e0 BHist.Empty) := by
  intro tree
  cases tree with
  | base carries =>
      exact Or.inl (And.intro carries (hsame_refl ledger))
  | meet leftTree rightTree =>
      exact Or.inr (Or.inl
        (Exists.intro _
          (Exists.intro _ (hsame_refl (BHist.e0 (append _ _))))))
  | union subtrees unionLaw =>
      exact Or.inr (Or.inr (Or.inl (hsame_refl (BHist.e1 BHist.Empty))))
  | bottom boundary =>
      exact Or.inr (Or.inr (Or.inr (hsame_refl (BHist.e0 BHist.Empty))))
  | top boundary =>
      exact Or.inr (Or.inr (Or.inl (hsame_refl (BHist.e1 BHist.Empty))))

theorem BHistFiniteBaseNeighborhood_finiteListIntersection_ledger_coverage
    (T : BHistIndexedOpenCarrier) (indices : ProbeBundle BHist)
    (ball : BHist -> BHist -> Prop) {i : T.OpenIx} {ledger : BHist}
    (unaryLedger : UnaryHistory ledger)
    (carries : BHistCarriesOpen T i (BHistFiniteBaseNeighborhood indices ball))
    (ballStable :
      forall {b x y : BHist}, InBundle b indices -> UnaryHistory x -> UnaryHistory y ->
        hsame x y -> (ball b x <-> ball b y)) :
    BHistUnaryTopologyLedgerRow T i (BHistFiniteBaseNeighborhood indices ball) ∧
      BHistGeneratedOpenExact T (BHistFiniteBaseNeighborhood indices ball) ∧
        (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
          (BHistFiniteBaseNeighborhood indices ball x <->
            BHistFiniteBaseNeighborhood indices ball y)) := by
  constructor
  · exact BHistUnaryTopologyLedgerRow.finiteListIntersection ledger unaryLedger carries
  · constructor
    · exact Exists.intro i carries
    · intro x y unaryX unaryY sameXY
      exact BHistFiniteBaseNeighborhood_classifier_transport indices ball ballStable
        unaryX unaryY sameXY

end BEDC.Derived.TopologyUp
