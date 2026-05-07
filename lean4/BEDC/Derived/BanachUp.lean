import BEDC.Derived.CompleteMetricUp
import BEDC.Derived.FieldUp
import BEDC.Derived.MetricUp
import BEDC.Derived.VecSpaceUp
import BEDC.Derived.RealUp

namespace BEDC.Derived.BanachUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.CompleteMetricUp
open BEDC.Derived.FieldUp
open BEDC.Derived.MetricUp
open BEDC.Derived.VecSpaceUp
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp

theorem BanachSingletonEmptyHistory_carrier_classifier {m n : BHist} :
    VecSpaceSingletonCarrier m -> VecSpaceSingletonCarrier n ->
      VecSpaceSingletonClassifier m n ∧ FieldSingletonClassifier m n ∧
        RealConstantHistoryClassifier (BHist.e1 (BHist.e1 BHist.Empty))
          (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro carrierM carrierN
  have sameMN : hsame m n := hsame_trans carrierM (hsame_symm carrierN)
  have vecRow : VecSpaceSingletonClassifier m n :=
    And.intro carrierM (And.intro carrierN sameMN)
  have fieldCarrierM : FieldSingletonCarrier m := carrierM
  have fieldCarrierN : FieldSingletonCarrier n := carrierN
  have fieldRow : FieldSingletonClassifier m n :=
    And.intro fieldCarrierM (And.intro fieldCarrierN sameMN)
  have positiveDenominator : PositiveUnaryDenominator (BHist.e1 BHist.Empty) :=
    Iff.mpr PositiveUnaryDenominator_e1_iff_unary unary_empty
  have intCarrier : BEDC.Derived.IntUp.IntCarrier BMark.b0 BHist.Empty :=
    And.intro (Or.inl rfl) unary_empty
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    Exists.intro BMark.b0
      (Exists.intro BHist.Empty
        (RatCarrier_of_int_positive_denominator intCarrier positiveDenominator))
  have ratRow : RatHistoryClassifier (BHist.e1 BHist.Empty)
      (BHist.e1 BHist.Empty) :=
    And.intro ratCarrier
      (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
  have realRow :
      RealConstantHistoryClassifier (BHist.e1 (BHist.e1 BHist.Empty))
        (BHist.e1 (BHist.e1 BHist.Empty)) :=
    Iff.mpr RealConstantHistoryClassifier_e1_iff_rat ratRow
  exact And.intro vecRow (And.intro fieldRow realRow)

def BanachSingletonCarrier (h : BHist) : Prop :=
  VecSpaceSingletonCarrier h ∧ MetricDistanceWitness h BHist.Empty BHist.Empty

def BanachSingletonClassifier (h k : BHist) : Prop :=
  BanachSingletonCarrier h ∧ BanachSingletonCarrier k ∧ hsame h k

def BanachSingletonBoundedLinearOperator (T : BHist -> BHist) (K ledger : BHist) : Prop :=
  hsame K BHist.Empty ∧ (hsame ledger BHist.Empty -> False) ∧
    forall {x : BHist}, BanachSingletonCarrier x -> BanachSingletonCarrier (T x)

theorem BanachSingletonBoundedLinearOperator_composition_closure {T S : BHist -> BHist}
    {K L Lambda Gamma : BHist} :
    BanachSingletonBoundedLinearOperator T K Lambda ->
      BanachSingletonBoundedLinearOperator S L Gamma ->
        BanachSingletonBoundedLinearOperator (fun x : BHist => S (T x)) BHist.Empty
          (BHist.e0 (append Gamma Lambda)) := by
  intro boundedT boundedS
  exact And.intro (hsame_refl BHist.Empty)
    (And.intro
      (fun ledgerEmpty => not_hsame_e0_empty ledgerEmpty)
      (by
        intro x carrierX
        exact boundedS.right.right (boundedT.right.right carrierX)))

theorem BanachSingletonCarrier_semanticNameCert :
    SemanticNameCert BanachSingletonCarrier BanachSingletonCarrier BanachSingletonCarrier
      BanachSingletonClassifier := by
  have emptyMetric : MetricDistanceWitness BHist.Empty BHist.Empty BHist.Empty :=
    (MetricDistanceWitness_empty_distance_iff (x := BHist.Empty) (y := BHist.Empty)).mpr
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
  have emptyCarrier : BanachSingletonCarrier BHist.Empty :=
    And.intro (hsame_refl BHist.Empty) emptyMetric
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
      equiv_refl := by
        intro h carrier
        exact And.intro carrier (And.intro carrier (hsame_refl h))
      equiv_symm := by
        intro h k same
        exact And.intro same.right.left
          (And.intro same.left (hsame_symm same.right.right))
      equiv_trans := by
        intro h k r sameHK sameKR
        exact And.intro sameHK.left
          (And.intro sameKR.right.left (hsame_trans sameHK.right.right sameKR.right.right))
      carrier_respects_equiv := by
        intro _h _k same _carrier
        exact same.right.left
    }
    pattern_sound := by
      intro _h carrier
      exact carrier
    ledger_sound := by
      intro _h carrier
      exact carrier
  }

theorem BanachRoot_carrier_classifier_obligation {h k : BHist} :
    BanachSingletonCarrier h -> BanachSingletonCarrier k ->
      BanachSingletonClassifier h k ∧ VecSpaceSingletonClassifier h k ∧
        FieldSingletonClassifier h k ∧
          RealConstantHistoryClassifier (BHist.e1 (BHist.e1 BHist.Empty))
            (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro carrierH carrierK
  have sameHK : hsame h k :=
    hsame_trans carrierH.left (hsame_symm carrierK.left)
  have baseRows :
      VecSpaceSingletonClassifier h k ∧ FieldSingletonClassifier h k ∧
        RealConstantHistoryClassifier (BHist.e1 (BHist.e1 BHist.Empty))
          (BHist.e1 (BHist.e1 BHist.Empty)) :=
    BanachSingletonEmptyHistory_carrier_classifier carrierH.left carrierK.left
  exact And.intro (And.intro carrierH (And.intro carrierK sameHK)) baseRows

theorem BanachSingleton_complete_metric_limit_empty_witness {s M : BHist -> BHist} :
    (forall {n : BHist}, UnaryHistory n -> hsame (s n) BHist.Empty) ->
      (forall {n : BHist}, UnaryHistory n ->
        RatHistoryClassifier BHist.Empty (M n)) ->
        CompleteMetricLimitWitness (fun h : BHist => hsame h BHist.Empty) s M
          BHist.Empty := by
  intro streamEmpty modulusClassified
  constructor
  · exact hsame_refl BHist.Empty
  · intro n nUnary sourceEmpty
    have distanceWitness : MetricDistanceWitness (s n) BHist.Empty BHist.Empty :=
      (MetricDistanceWitness_empty_distance_iff (x := s n) (y := BHist.Empty)).mpr
        (And.intro sourceEmpty (hsame_refl BHist.Empty))
    have continuation : Cont (s n) BHist.Empty BHist.Empty := by
      exact cont_right_unit_iff.mpr (hsame_symm sourceEmpty)
    exact Exists.intro BHist.Empty
        (And.intro distanceWitness (And.intro continuation (modulusClassified nUnary)))

theorem BanachSingleton_standard_bridge_soundness {h : BHist} {s M : BHist -> BHist} :
    BanachSingletonCarrier h ->
      (forall {n : BHist}, UnaryHistory n -> hsame (s n) BHist.Empty) ->
        (forall {n : BHist}, UnaryHistory n -> RatHistoryClassifier BHist.Empty (M n)) ->
          BanachSingletonClassifier h BHist.Empty ∧
            MetricDistanceWitness h BHist.Empty BHist.Empty ∧
              CompleteMetricLimitWitness BanachSingletonCarrier s M BHist.Empty := by
  intro carrierH streamEmpty modulusClassified
  have emptyMetric : MetricDistanceWitness BHist.Empty BHist.Empty BHist.Empty :=
    (MetricDistanceWitness_empty_distance_iff (x := BHist.Empty) (y := BHist.Empty)).mpr
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
  have emptyCarrier : BanachSingletonCarrier BHist.Empty :=
    And.intro (hsame_refl BHist.Empty) emptyMetric
  have classified : BanachSingletonClassifier h BHist.Empty :=
    And.intro carrierH (And.intro emptyCarrier carrierH.left)
  have limitWitness :
      CompleteMetricLimitWitness BanachSingletonCarrier s M BHist.Empty := by
    constructor
    · exact emptyCarrier
    · intro n nUnary sourceCarrier
      have sourceEmpty : hsame (s n) BHist.Empty := streamEmpty nUnary
      have distanceWitness : MetricDistanceWitness (s n) BHist.Empty BHist.Empty :=
        (MetricDistanceWitness_empty_distance_iff (x := s n) (y := BHist.Empty)).mpr
          (And.intro sourceEmpty (hsame_refl BHist.Empty))
      have continuation : Cont (s n) BHist.Empty BHist.Empty := by
        exact cont_right_unit_iff.mpr (hsame_symm sourceEmpty)
      exact Exists.intro BHist.Empty
        (And.intro distanceWitness (And.intro continuation (modulusClassified nUnary)))
  exact And.intro classified (And.intro carrierH.right limitWitness)

theorem BanachSingleton_norm_distance_zero_exactness {x y : BHist} :
    BanachSingletonCarrier x -> BanachSingletonCarrier y ->
      MetricDistanceWitness x y BHist.Empty ->
        VecSpaceSingletonClassifier x y ∧ hsame x y := by
  intro carrierX carrierY distanceZero
  have endpoints :
      hsame x BHist.Empty ∧ hsame y BHist.Empty :=
    (MetricDistanceWitness_empty_distance_iff (x := x) (y := y)).mp distanceZero
  have sameXY : hsame x y :=
    hsame_trans endpoints.left (hsame_symm endpoints.right)
  exact And.intro
    (And.intro carrierX.left (And.intro carrierY.left sameXY))
    sameXY

theorem BanachSingleton_metric_distance_empty_iff_classifier {x y : BHist} :
    BanachSingletonCarrier x -> BanachSingletonCarrier y ->
      (MetricDistanceWitness x y BHist.Empty ↔ BanachSingletonClassifier x y) := by
  intro carrierX carrierY
  constructor
  · intro distanceZero
    have exactness :=
      BanachSingleton_norm_distance_zero_exactness carrierX carrierY distanceZero
    exact And.intro carrierX (And.intro carrierY exactness.right)
  · intro _classified
    exact MetricDistanceWitness_empty_distance_iff.mpr
      (And.intro carrierX.left carrierY.left)

theorem BanachSingleton_root_norm_metric_obligation {h k d : BHist} :
    BanachSingletonCarrier h -> BanachSingletonCarrier k -> MetricDistanceWitness h k d ->
      hsame d BHist.Empty ∧ BanachSingletonClassifier h k ∧
        MetricDistanceWitness h k BHist.Empty := by
  intro carrierH carrierK distance
  have hEndpoints :
      hsame h BHist.Empty ∧ hsame BHist.Empty BHist.Empty :=
    (MetricDistanceWitness_empty_distance_iff (x := h) (y := BHist.Empty)).mp carrierH.right
  have kEndpoints :
      hsame k BHist.Empty ∧ hsame BHist.Empty BHist.Empty :=
    (MetricDistanceWitness_empty_distance_iff (x := k) (y := BHist.Empty)).mp carrierK.right
  have emptyDistance : MetricDistanceWitness h k BHist.Empty :=
    (MetricDistanceWitness_empty_distance_iff (x := h) (y := k)).mpr
      (And.intro hEndpoints.left kEndpoints.left)
  have sameDistance : hsame d BHist.Empty :=
    MetricDistanceWitness_hsame_result_deterministic
      (hsame_refl h) (hsame_refl k) distance emptyDistance
  have sameHK : hsame h k :=
    hsame_trans hEndpoints.left (hsame_symm kEndpoints.left)
  have classified : BanachSingletonClassifier h k :=
    And.intro carrierH (And.intro carrierK sameHK)
  exact And.intro sameDistance (And.intro classified emptyDistance)

theorem BanachSingleton_limit_classifier_uniqueness
    {s M0 M1 : BHist -> BHist} {l0 l1 : BHist} :
    CompleteMetricLimitWitness BanachSingletonCarrier s M0 l0 ->
      CompleteMetricLimitWitness BanachSingletonCarrier s M1 l1 ->
        hsame l0 l1 ∧ VecSpaceSingletonClassifier l0 l1 ∧
          BanachSingletonClassifier l0 l1 ∧
            Cont l0 BHist.Empty l0 ∧ Cont l1 BHist.Empty l1 := by
  intro witness0 witness1
  have limit0Vec : VecSpaceSingletonCarrier l0 := witness0.left.left
  have limit1Vec : VecSpaceSingletonCarrier l1 := witness1.left.left
  have sameLimits : hsame l0 l1 :=
    hsame_trans limit0Vec (hsame_symm limit1Vec)
  have vecClassified : VecSpaceSingletonClassifier l0 l1 :=
    And.intro limit0Vec (And.intro limit1Vec sameLimits)
  have banachClassified : BanachSingletonClassifier l0 l1 :=
    And.intro witness0.left (And.intro witness1.left sameLimits)
  exact And.intro sameLimits
    (And.intro vecClassified
      (And.intro banachClassified
        (And.intro (cont_right_unit l0) (cont_right_unit l1))))

theorem BanachSingleton_limit_classifier_unique
    {s M0 M1 : BHist -> BHist} {l0 l1 : BHist} :
    CompleteMetricLimitWitness BanachSingletonCarrier s M0 l0 ->
      CompleteMetricLimitWitness BanachSingletonCarrier s M1 l1 ->
        BanachSingletonClassifier l0 l1 ∧
          MetricDistanceWitness l0 l1 BHist.Empty := by
  intro witness0 witness1
  have carrier0 : BanachSingletonCarrier l0 := witness0.left
  have carrier1 : BanachSingletonCarrier l1 := witness1.left
  have sameL0 : hsame l0 BHist.Empty := carrier0.left
  have sameL1 : hsame l1 BHist.Empty := carrier1.left
  have sameLimits : hsame l0 l1 := hsame_trans sameL0 (hsame_symm sameL1)
  have distance :
      MetricDistanceWitness l0 l1 BHist.Empty :=
    MetricDistanceWitness_empty_distance_iff.mpr (And.intro sameL0 sameL1)
  exact And.intro
    (And.intro carrier0 (And.intro carrier1 sameLimits))
    distance

theorem BanachSingleton_regular_cauchy_stream_transport {s s' M M' : BHist -> BHist}
    {limit limit' : BHist} :
    (forall {n : BHist}, UnaryHistory n -> hsame (s n) (s' n)) ->
      (forall {n : BHist}, UnaryHistory n -> hsame (M n) (M' n)) ->
        hsame limit limit' -> CompleteMetricLimitWitness BanachSingletonCarrier s M limit ->
          CompleteMetricLimitWitness BanachSingletonCarrier s' M' limit' ∧
            BanachSingletonClassifier limit limit' := by
  intro streamTransport modulusTransport sameLimit witness
  have carrierTransport :
      forall {h k : BHist}, hsame h k -> BanachSingletonCarrier h ->
        BanachSingletonCarrier k := by
    intro h k sameHK carrierH
    have sameKEmpty : hsame k BHist.Empty :=
      hsame_trans (hsame_symm sameHK) carrierH.left
    have metricK :
        MetricDistanceWitness k BHist.Empty BHist.Empty :=
      MetricDistanceWitness_empty_distance_iff.mpr
        (And.intro sameKEmpty (hsame_refl BHist.Empty))
    exact And.intro sameKEmpty metricK
  have transported :
      CompleteMetricLimitWitness BanachSingletonCarrier s' M' limit' :=
    CompleteMetricLimitWitness_hsame_transport carrierTransport streamTransport
      modulusTransport sameLimit witness
  have classified : BanachSingletonClassifier limit limit' :=
    And.intro witness.left (And.intro transported.left sameLimit)
  exact And.intro transported classified

theorem BanachSingleton_regular_cauchy_stream_input {s M : BHist -> BHist} :
    (forall {n : BHist}, UnaryHistory n -> BanachSingletonCarrier (s n)) ->
      (forall {n : BHist}, UnaryHistory n -> RatHistoryClassifier BHist.Empty (M n)) ->
        CompleteMetricLimitWitness BanachSingletonCarrier s M BHist.Empty ∧
          (forall {n : BHist}, UnaryHistory n -> exists d : BHist,
            MetricDistanceWitness (s n) BHist.Empty d ∧ Cont (s n) BHist.Empty d ∧
              RatHistoryClassifier d (M n)) := by
  intro streamCarrier modulusClassified
  have emptyMetric : MetricDistanceWitness BHist.Empty BHist.Empty BHist.Empty :=
    MetricDistanceWitness_empty_distance_iff.mpr
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
  have limitCarrier : BanachSingletonCarrier BHist.Empty :=
    And.intro (hsame_refl BHist.Empty) emptyMetric
  have readback :
      forall {n : BHist}, UnaryHistory n -> exists d : BHist,
        MetricDistanceWitness (s n) BHist.Empty d ∧ Cont (s n) BHist.Empty d ∧
          RatHistoryClassifier d (M n) := by
    intro n nUnary
    have sourceCarrier : BanachSingletonCarrier (s n) := streamCarrier nUnary
    have distanceWitness : MetricDistanceWitness (s n) BHist.Empty BHist.Empty :=
      MetricDistanceWitness_empty_distance_iff.mpr
        (And.intro sourceCarrier.left (hsame_refl BHist.Empty))
    have continuation : Cont (s n) BHist.Empty BHist.Empty :=
      cont_right_unit_iff.mpr (hsame_symm sourceCarrier.left)
    exact Exists.intro BHist.Empty
      (And.intro distanceWitness (And.intro continuation (modulusClassified nUnary)))
  have limitWitness : CompleteMetricLimitWitness BanachSingletonCarrier s M BHist.Empty := by
    constructor
    · exact limitCarrier
    · intro n nUnary _sourceCarrier
      exact readback nUnary
  exact And.intro limitWitness readback

theorem BanachSingletonBoundedLinearOperator_limit_witness_transport
    {T : BHist -> BHist} {K Lambda : BHist} {s M : BHist -> BHist} :
    BanachSingletonBoundedLinearOperator T K Lambda ->
      (forall {n : BHist}, UnaryHistory n -> BanachSingletonCarrier (s n)) ->
        CompleteMetricLimitWitness BanachSingletonCarrier s M BHist.Empty ->
          CompleteMetricLimitWitness BanachSingletonCarrier (fun n : BHist => T (s n)) M
              (T BHist.Empty) ∧
            BanachSingletonClassifier (T BHist.Empty) BHist.Empty := by
  intro boundedT sourceCarrier sourceWitness
  have operatorClosure :
      forall {x : BHist}, BanachSingletonCarrier x -> BanachSingletonCarrier (T x) :=
    boundedT.right.right
  have emptyMetric : MetricDistanceWitness BHist.Empty BHist.Empty BHist.Empty :=
    MetricDistanceWitness_empty_distance_iff.mpr
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
  have emptyCarrier : BanachSingletonCarrier BHist.Empty :=
    And.intro (hsame_refl BHist.Empty) emptyMetric
  have limitCarrier : BanachSingletonCarrier (T BHist.Empty) :=
    operatorClosure emptyCarrier
  have transportedWitness :
      CompleteMetricLimitWitness BanachSingletonCarrier (fun n : BHist => T (s n)) M
        (T BHist.Empty) := by
    constructor
    · exact limitCarrier
    · intro n nUnary transportedSource
      have sourceData : BanachSingletonCarrier (s n) := sourceCarrier nUnary
      cases sourceWitness.right nUnary sourceData with
      | intro d distanceData =>
          have transportedDistance :
              MetricDistanceWitness (T (s n)) (T BHist.Empty) BHist.Empty :=
            MetricDistanceWitness_empty_distance_iff.mpr
              (And.intro transportedSource.left limitCarrier.left)
          have transportedCont : Cont (T (s n)) (T BHist.Empty) BHist.Empty :=
            transportedDistance.right.right.right
          have sameD : hsame d BHist.Empty :=
            MetricDistanceWitness_hsame_result_deterministic (hsame_refl (s n))
              (hsame_refl BHist.Empty) distanceData.left
              (MetricDistanceWitness_empty_distance_iff.mpr
                (And.intro sourceData.left (hsame_refl BHist.Empty)))
          have transportedModulus : RatHistoryClassifier BHist.Empty (M n) :=
            RatHistoryClassifier_hsame_transport sameD (hsame_refl (M n))
              distanceData.right.right
          exact Exists.intro BHist.Empty
            (And.intro transportedDistance
              (And.intro transportedCont transportedModulus))
  have classified : BanachSingletonClassifier (T BHist.Empty) BHist.Empty :=
    And.intro limitCarrier (And.intro emptyCarrier limitCarrier.left)
  exact And.intro transportedWitness classified

theorem BanachSingletonBoundedLinearOperator_composition_cauchy_transport
    {T S : BHist -> BHist} {K L Lambda Gamma : BHist} {s M : BHist -> BHist} :
    BanachSingletonBoundedLinearOperator T K Lambda ->
      BanachSingletonBoundedLinearOperator S L Gamma ->
        (forall {n : BHist}, UnaryHistory n -> BanachSingletonCarrier (s n)) ->
          CompleteMetricLimitWitness BanachSingletonCarrier s M BHist.Empty ->
            CompleteMetricLimitWitness BanachSingletonCarrier
                (fun n : BHist => S (T (s n))) M (S BHist.Empty) ∧
              BanachSingletonClassifier (S BHist.Empty) BHist.Empty := by
  intro boundedT boundedS sourceCarrier sourceWitness
  have transportedT :
      CompleteMetricLimitWitness BanachSingletonCarrier (fun n : BHist => T (s n)) M
          (T BHist.Empty) ∧
        BanachSingletonClassifier (T BHist.Empty) BHist.Empty :=
    BanachSingletonBoundedLinearOperator_limit_witness_transport boundedT sourceCarrier
      sourceWitness
  have sourceCarrierT :
      forall {n : BHist}, UnaryHistory n -> BanachSingletonCarrier (T (s n)) := by
    intro n nUnary
    exact boundedT.right.right (sourceCarrier nUnary)
  have sameLimitT : hsame (T BHist.Empty) BHist.Empty :=
    transportedT.right.right.right
  have alignedT :
      CompleteMetricLimitWitness BanachSingletonCarrier (fun n : BHist => T (s n)) M
        BHist.Empty := by
    have carrierTransport :
        forall {h k : BHist}, hsame h k -> BanachSingletonCarrier h ->
          BanachSingletonCarrier k := by
      intro h k sameHK carrierH
      have sameKEmpty : hsame k BHist.Empty :=
        hsame_trans (hsame_symm sameHK) carrierH.left
      have metricK : MetricDistanceWitness k BHist.Empty BHist.Empty :=
        MetricDistanceWitness_empty_distance_iff.mpr
          (And.intro sameKEmpty (hsame_refl BHist.Empty))
      exact And.intro sameKEmpty metricK
    exact CompleteMetricLimitWitness_hsame_transport carrierTransport
      (fun {n : BHist} (_nUnary : UnaryHistory n) => hsame_refl (T (s n)))
      (fun {n : BHist} (_nUnary : UnaryHistory n) => hsame_refl (M n))
      sameLimitT transportedT.left
  exact BanachSingletonBoundedLinearOperator_limit_witness_transport boundedS sourceCarrierT
    alignedT

end BEDC.Derived.BanachUp
