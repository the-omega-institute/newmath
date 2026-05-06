import BEDC.Derived.TopologyUp.Core
import BEDC.Derived.TopologyUp.Singleton

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Bundle
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

theorem BHistFiniteBaseNeighborhood_singleton_ledger_coverage
    (T : BHistIndexedOpenCarrier) (ball : BHist -> BHist -> Prop)
    {center ledger : BHist} {i : T.OpenIx}
    (unaryLedger : UnaryHistory ledger)
    (carries : BHistCarriesOpen T i (fun x : BHist => ball center x))
    (ballStable :
      forall {x y : BHist},
        UnaryHistory x -> UnaryHistory y -> hsame x y -> (ball center x <-> ball center y)) :
    BHistUnaryTopologyLedgerRow T i
        (BHistFiniteBaseNeighborhood
          (ProbeBundle.Bcons center (ProbeBundle.Bnil : ProbeBundle BHist)) ball) ∧
      BHistGeneratedOpenExact T
        (BHistFiniteBaseNeighborhood
          (ProbeBundle.Bcons center (ProbeBundle.Bnil : ProbeBundle BHist)) ball) ∧
        (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
          (BHistFiniteBaseNeighborhood
              (ProbeBundle.Bcons center (ProbeBundle.Bnil : ProbeBundle BHist)) ball x <->
            BHistFiniteBaseNeighborhood
              (ProbeBundle.Bcons center (ProbeBundle.Bnil : ProbeBundle BHist)) ball y)) := by
  let singleton : ProbeBundle BHist :=
    ProbeBundle.Bcons center (ProbeBundle.Bnil : ProbeBundle BHist)
  have singletonCarries :
      BHistCarriesOpen T i (BHistFiniteBaseNeighborhood singleton ball) := by
    intro x unaryX
    have carryCenter : ball center x <-> T.OpenAt i x :=
      carries unaryX
    constructor
    · intro neighborhood
      exact Iff.mp carryCenter (neighborhood center (Or.inl rfl))
    · intro openAt p inSingleton
      cases inSingleton with
      | inl samePCenter =>
          cases samePCenter
          exact Iff.mpr carryCenter openAt
      | inr inNil =>
          cases inNil
  have singletonStable :
      forall {b x y : BHist}, InBundle b singleton -> UnaryHistory x -> UnaryHistory y ->
        hsame x y -> (ball b x <-> ball b y) := by
    intro b x y inSingleton unaryX unaryY sameXY
    cases inSingleton with
    | inl sameBCenter =>
        cases sameBCenter
        exact ballStable unaryX unaryY sameXY
    | inr inNil =>
        cases inNil
  constructor
  · exact BHistUnaryTopologyLedgerRow.singletonMetricBall ledger unaryLedger singletonCarries
  · constructor
    · exact Exists.intro i singletonCarries
    · exact BHistFiniteBaseNeighborhood_classifier_transport singleton ball singletonStable

end BEDC.Derived.TopologyUp
