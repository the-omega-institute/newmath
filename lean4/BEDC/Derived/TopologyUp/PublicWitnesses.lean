import BEDC.Derived.TopologyUp

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

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

theorem BHistLedgerGeneratedOpen_row_coverage (T : BHistIndexedOpenCarrier)
    {i : T.OpenIx} {U : BHist -> Prop} {ledger : BHist} :
    BHistLedgerPublicOpenTree T i U ledger ->
      BHistGeneratedOpenExact T U ∧ BHistCarriesOpen T i U ∧
        (exists r : BHist, BHistLedgerPublicOpenTree T i U r) ∧
          (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
            (U x <-> U y)) := by
  intro tree
  have carries : BHistCarriesOpen T i U :=
    BHistPublicOpenTree_carries_open T tree
  exact And.intro (Exists.intro i carries)
    (And.intro carries
      (And.intro (Exists.intro ledger tree)
        (BHistCarriesOpen_classifier_transport T carries)))

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

theorem BHistUnaryTopologyLedgerRow_metric_generated_obligation_surface
    (T : BHistIndexedOpenCarrier) {i j : T.OpenIx} {U V : BHist -> Prop} :
    BHistUnaryTopologyLedgerRow T i U -> BHistUnaryTopologyLedgerRow T j V ->
      (BHistGeneratedOpenExact T U ∧
          (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
            (U x <-> U y))) ∧
        (BHistGeneratedOpenExact T V ∧
          (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
            (V x <-> V y))) ∧
        BHistCarriesOpen T (T.meet i j) (fun x : BHist => U x ∧ V x) ∧
        BHistGeneratedOpenExact T (fun x : BHist => U x ∧ V x) ∧
        (exists ledger : BHist, UnaryHistory ledger) := by
  intro rowU rowV
  have transportU :
      forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
        (U x <-> U y) :=
    BHistUnaryTopologyLedgerRow_classifier_transport T rowU
  have transportV :
      forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
        (V x <-> V y) :=
    BHistUnaryTopologyLedgerRow_classifier_transport T rowV
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
  have meetClosure :=
    BHistIndexedOpen_finite_intersection_closure (T := T) (i := i) (j := j)
      (U := U) (V := V) carriesU carriesV
  have exactU : BHistGeneratedOpenExact T U :=
    Exists.intro i carriesU
  have exactV : BHistGeneratedOpenExact T V :=
    Exists.intro j carriesV
  have exactMeet : BHistGeneratedOpenExact T (fun x : BHist => U x ∧ V x) :=
    Exists.intro (T.meet i j) meetClosure.left
  have ledgerWitness : exists ledger : BHist, UnaryHistory ledger := by
    cases rowU with
    | singletonMetricBall ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | finiteListIntersection ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | binaryGeneratedMeet ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | arbitraryUnion ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | bottom ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | top ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
  exact And.intro (And.intro exactU transportU)
    (And.intro (And.intro exactV transportV)
      (And.intro meetClosure.left (And.intro exactMeet ledgerWitness)))

end BEDC.Derived.TopologyUp
