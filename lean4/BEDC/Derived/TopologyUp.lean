import BEDC.Derived.TopologyUp.Core
import BEDC.Derived.TopologyUp.Singleton

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem BHistUnaryTopologyLedgerRow_classifier_transport (T : BHistIndexedOpenCarrier)
    {i : T.OpenIx} {U : BHist -> Prop} :
    BHistUnaryTopologyLedgerRow T i U ->
      forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y -> (U x <-> U y) := by
  intro row
  cases row with
  | singletonMetricBall ledger unaryLedger carries =>
      exact BHistCarriesOpen_classifier_transport T carries
  | finiteListIntersection ledger unaryLedger carries =>
      exact BHistCarriesOpen_classifier_transport T carries
  | binaryGeneratedMeet ledger unaryLedger carries =>
      exact BHistCarriesOpen_classifier_transport T carries
  | arbitraryUnion ledger unaryLedger carries =>
      exact BHistCarriesOpen_classifier_transport T carries
  | bottom ledger unaryLedger carries =>
      exact BHistCarriesOpen_classifier_transport T carries
  | top ledger unaryLedger carries =>
      exact BHistCarriesOpen_classifier_transport T carries


theorem BHistFiniteBaseNeighborhood_bundleAppend_carries_intersection
    (T : BHistIndexedOpenCarrier) (left right : ProbeBundle BHist)
    (ball : BHist -> BHist -> Prop) {i j : T.OpenIx} :
    BHistCarriesOpen T i (BHistFiniteBaseNeighborhood left ball) ->
      BHistCarriesOpen T j (BHistFiniteBaseNeighborhood right ball) ->
        BHistCarriesOpen T (T.meet i j)
          (BHistFiniteBaseNeighborhood (bundleAppend left right) ball) := by
  intro carryLeft carryRight x unaryX
  have closure :
      BHistCarriesOpen T (T.meet i j)
          (fun x : BHist =>
            BHistFiniteBaseNeighborhood left ball x ∧
              BHistFiniteBaseNeighborhood right ball x) ∧
        (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
          ((BHistFiniteBaseNeighborhood left ball x ∧
              BHistFiniteBaseNeighborhood right ball x) <->
            (BHistFiniteBaseNeighborhood left ball y ∧
              BHistFiniteBaseNeighborhood right ball y))) :=
    BHistIndexedOpen_finite_intersection_closure (T := T) (i := i) (j := j)
      (U := fun x : BHist => BHistFiniteBaseNeighborhood left ball x)
      (V := fun x : BHist => BHistFiniteBaseNeighborhood right ball x) carryLeft
      carryRight
  have meetClosure :
      BHistCarriesOpen T (T.meet i j)
        (fun x : BHist =>
          BHistFiniteBaseNeighborhood left ball x ∧
            BHistFiniteBaseNeighborhood right ball x) :=
    closure.left
  have appendSplit :
      BHistFiniteBaseNeighborhood (bundleAppend left right) ball x <->
        BHistFiniteBaseNeighborhood left ball x ∧
          BHistFiniteBaseNeighborhood right ball x := by
    constructor
    · intro appendNeighborhood
      constructor
      · intro p memberLeft
        have memberAppend : InBundle p (bundleAppend left right) :=
          Iff.mpr (inBundle_bundleAppend_iff (p := p) (left := left) (right := right))
            (Or.inl memberLeft)
        exact appendNeighborhood p memberAppend
      · intro p memberRight
        have memberAppend : InBundle p (bundleAppend left right) :=
          Iff.mpr (inBundle_bundleAppend_iff (p := p) (left := left) (right := right))
            (Or.inr memberRight)
        exact appendNeighborhood p memberAppend
    · intro both p memberAppend
      cases Iff.mp (inBundle_bundleAppend_iff (p := p) (left := left) (right := right))
          memberAppend with
      | inl memberLeft =>
          exact both.left p memberLeft
      | inr memberRight =>
          exact both.right p memberRight
  have meetCarries :
      (BHistFiniteBaseNeighborhood left ball x ∧
          BHistFiniteBaseNeighborhood right ball x) <->
        T.OpenAt (T.meet i j) x :=
    meetClosure unaryX
  constructor
  · intro appendNeighborhood
    exact Iff.mp meetCarries (Iff.mp appendSplit appendNeighborhood)
  · intro openMeet
    exact Iff.mpr appendSplit (Iff.mpr meetCarries openMeet)

theorem BHistLedgerPublicOpenTree_meet_ledger_constructor (T : BHistIndexedOpenCarrier)
    {i j : T.OpenIx} {U V : BHist -> Prop} {leftLedger rightLedger : BHist} :
    BHistLedgerPublicOpenTree T i U leftLedger ->
      BHistLedgerPublicOpenTree T j V rightLedger ->
        BHistLedgerPublicOpenTree T (T.meet i j) (fun x : BHist => U x ∧ V x)
            (BHist.e0 (append leftLedger rightLedger)) ∧
          BHistCarriesOpen T (T.meet i j) (fun x : BHist => U x ∧ V x) := by
  intro leftTree rightTree
  have meetTree :
      BHistLedgerPublicOpenTree T (T.meet i j) (fun x : BHist => U x ∧ V x)
        (BHist.e0 (append leftLedger rightLedger)) :=
    BHistLedgerPublicOpenTree.meet leftTree rightTree
  exact And.intro meetTree (BHistPublicOpenTree_carries_open T meetTree)

theorem BHistUnaryTopologyDepsReady_obligation_package (T : BHistIndexedOpenCarrier)
    {i j : T.OpenIx} {U V : BHist -> Prop} :
    BHistUnaryTopologyLedgerRow T i U -> BHistUnaryTopologyLedgerRow T j V ->
      (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
        (U x <-> U y)) ∧
        BHistCarriesOpen T (T.meet i j) (fun x : BHist => U x ∧ V x) ∧
          (exists ledger : BHist, UnaryHistory ledger) := by
  intro rowU rowV
  have transportU :
      forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
        (U x <-> U y) :=
    BHistUnaryTopologyLedgerRow_classifier_transport T rowU
  have carriesU : BHistCarriesOpen T i U := by
    cases rowU with
    | singletonMetricBall _ _ carries => exact carries
    | finiteListIntersection _ _ carries => exact carries
    | binaryGeneratedMeet _ _ carries => exact carries
    | arbitraryUnion _ _ carries => exact carries
    | bottom _ _ carries => exact carries
    | top _ _ carries => exact carries
  have carriesV : BHistCarriesOpen T j V := by
    cases rowV with
    | singletonMetricBall _ _ carries => exact carries
    | finiteListIntersection _ _ carries => exact carries
    | binaryGeneratedMeet _ _ carries => exact carries
    | arbitraryUnion _ _ carries => exact carries
    | bottom _ _ carries => exact carries
    | top _ _ carries => exact carries
  have meetClosure :
      BHistCarriesOpen T (T.meet i j) (fun x : BHist => U x ∧ V x) :=
    (BHistIndexedOpen_finite_intersection_closure T carriesU carriesV).left
  have ledgerWitness : exists ledger : BHist, UnaryHistory ledger := by
    cases rowU with
    | singletonMetricBall ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | finiteListIntersection ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | binaryGeneratedMeet ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | arbitraryUnion ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | bottom ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | top ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
  exact And.intro transportU (And.intro meetClosure ledgerWitness)

end BEDC.Derived.TopologyUp
