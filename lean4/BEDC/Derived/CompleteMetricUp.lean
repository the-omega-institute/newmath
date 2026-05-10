import BEDC.Derived.MetricUp
import BEDC.Derived.MetricUp.Transport
import BEDC.Derived.RatUp
import BEDC.FKernel.Cont.Units
import BEDC.Derived.RatUp.HistoryClassifier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CompleteMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.MetricUp
open BEDC.Derived.RatUp

def CompleteMetricLimitWitness (X : BHist -> Prop) (s M : BHist -> BHist)
    (limit : BHist) : Prop :=
  X limit ∧
    forall {n : BHist}, UnaryHistory n -> X (s n) ->
      exists d : BHist,
        MetricDistanceWitness (s n) limit d ∧
          Cont (s n) limit d ∧ RatHistoryClassifier d (M n)

theorem CompleteMetricLimitWitness_empty_limit_distance_cont_readback
    {X : BHist -> Prop} {s M : BHist -> BHist} :
    CompleteMetricLimitWitness X s M BHist.Empty ->
      forall {n : BHist}, UnaryHistory n -> X (s n) ->
        exists d : BHist,
          Cont (s n) BHist.Empty d ∧ hsame d (s n) ∧ RatHistoryClassifier d (M n) := by
  intro witness n nUnary source
  cases witness.right nUnary source with
  | intro d distanceData =>
      have boundary :
          UnaryHistory (s n) ∧ hsame d (s n) :=
        (MetricDistanceWitness_empty_right_iff (x := s n) (d := d)).mp distanceData.left
      exact ⟨d, distanceData.right.left, boundary.right, distanceData.right.right⟩

theorem CompleteMetricLimitWitness_empty_limit_rat_positive
    {X : BHist -> Prop} {s M : BHist -> BHist} :
    CompleteMetricLimitWitness X s M BHist.Empty ->
      forall {n : BHist}, UnaryHistory n -> X (s n) ->
        exists d : BHist,
          PositiveUnaryDenominator d ∧ PositiveUnaryDenominator (M n) ∧
            Cont (s n) BHist.Empty d := by
  intro witness n nUnary source
  cases witness.right nUnary source with
  | intro d distanceData =>
      have positives :
          PositiveUnaryDenominator d ∧ PositiveUnaryDenominator (M n) :=
        RatHistoryClassifier_positive_denominators distanceData.right.right
      exact ⟨d, positives.left, positives.right, distanceData.right.left⟩

theorem CompleteMetricLimitWitness_hsame_transport {X : BHist -> Prop}
    {s s' M M' : BHist -> BHist} {limit limit' : BHist} :
    (forall {h k : BHist}, hsame h k -> X h -> X k) ->
      (forall {n : BHist}, UnaryHistory n -> hsame (s n) (s' n)) ->
        (forall {n : BHist}, UnaryHistory n -> hsame (M n) (M' n)) ->
          hsame limit limit' -> CompleteMetricLimitWitness X s M limit ->
            CompleteMetricLimitWitness X s' M' limit' := by
  intro carrierTransport streamTransport modulusTransport sameLimit witness
  constructor
  · exact carrierTransport sameLimit witness.left
  · intro n nUnary source
    have sourceOld : X (s n) :=
      carrierTransport (hsame_symm (streamTransport nUnary)) source
    cases witness.right nUnary sourceOld with
    | intro d distanceData =>
        exact ⟨d,
          MetricDistanceWitness_hsame_fields_transport (streamTransport nUnary) sameLimit
            (hsame_refl d) distanceData.left,
          MetricDistanceWitness_cont_hsame_transport (streamTransport nUnary) sameLimit
            (hsame_refl d) distanceData.left,
        RatHistoryClassifier_hsame_transport (hsame_refl d) (modulusTransport nUnary)
          distanceData.right.right⟩

theorem CompleteMetricLimitWitness_tolerance_weakening {X : BHist -> Prop}
    {s M eps : BHist -> BHist} {limit : BHist} :
    (forall {n : BHist}, UnaryHistory n -> RatHistoryClassifier (M n) (eps n)) ->
      CompleteMetricLimitWitness X s M limit ->
        CompleteMetricLimitWitness X s eps limit := by
  intro tolerance witness
  constructor
  · exact witness.left
  · intro n nUnary source
    cases witness.right nUnary source with
    | intro d distanceData =>
        exact ⟨d, distanceData.left, distanceData.right.left,
          RatHistoryClassifier_trans distanceData.right.right (tolerance nUnary)⟩

theorem CompleteMetricLimitWitness_distance_modulus_positive_denominators
    {X : BHist -> Prop} {s M : BHist -> BHist} {limit n : BHist} :
    CompleteMetricLimitWitness X s M limit -> UnaryHistory n -> X (s n) ->
      exists d : BHist,
        MetricDistanceWitness (s n) limit d ∧ Cont (s n) limit d ∧
          PositiveUnaryDenominator d ∧ PositiveUnaryDenominator (M n) ∧
            RatHistoryClassifier d (M n) := by
  intro witness nUnary source
  cases witness.right nUnary source with
  | intro d distanceData =>
      have positives :
          PositiveUnaryDenominator d ∧ PositiveUnaryDenominator (M n) :=
        RatHistoryClassifier_positive_denominators distanceData.right.right
      exact Exists.intro d
        (And.intro distanceData.left
          (And.intro distanceData.right.left
            (And.intro positives.left
              (And.intro positives.right distanceData.right.right))))

theorem CompleteMetricLimitWitness_modulus_not_empty
    {X : BHist -> Prop} {s M : BHist -> BHist} {limit n : BHist} :
    CompleteMetricLimitWitness X s M limit -> UnaryHistory n -> X (s n) ->
      hsame (M n) BHist.Empty -> False := by
  intro witness nUnary source sameEmpty
  cases witness.right nUnary source with
  | intro _d distanceData =>
      have positives :
          PositiveUnaryDenominator _d ∧ PositiveUnaryDenominator (M n) :=
        RatHistoryClassifier_positive_denominators distanceData.right.right
      exact PositiveUnaryDenominator_not_empty positives.right sameEmpty

theorem CompleteMetricLimitWitness_observation_bound_transport {X : BHist -> Prop}
    (carrierTransport : forall {h k : BHist}, hsame h k -> X h -> X k)
    {s s' M M' : BHist -> BHist} {limit limit' n : BHist} :
    UnaryHistory n -> CompleteMetricLimitWitness X s M limit -> X (s' n) ->
      hsame (s n) (s' n) -> hsame limit limit' -> hsame (M n) (M' n) ->
        exists d : BHist,
          MetricDistanceWitness (s' n) limit' d ∧
            Cont (s' n) limit' d ∧ RatHistoryClassifier d (M' n) := by
  intro nUnary witness source sameSource sameLimit sameModulus
  have sourceOld : X (s n) :=
    carrierTransport (hsame_symm sameSource) source
  cases witness.right nUnary sourceOld with
  | intro d distanceData =>
      exact ⟨d,
        MetricDistanceWitness_hsame_fields_transport sameSource sameLimit
          (hsame_refl d) distanceData.left,
        MetricDistanceWitness_cont_hsame_transport sameSource sameLimit
          (hsame_refl d) distanceData.left,
        RatHistoryClassifier_hsame_transport (hsame_refl d) sameModulus
          distanceData.right.right⟩

theorem CompleteMetricLimitWitness_name_certificate {X : BHist -> Prop}
    (carrierTransport : ∀ {h k : BHist}, hsame h k -> X h -> X k)
    {s M : BHist -> BHist} {limit : BHist}
    (witness : CompleteMetricLimitWitness X s M limit) :
    SemanticNameCert (CompleteMetricLimitWitness X s M) (CompleteMetricLimitWitness X s M)
      (CompleteMetricLimitWitness X s M) hsame := by
  constructor
  · constructor
    · exact Exists.intro limit witness
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      exact CompleteMetricLimitWitness_hsame_transport carrierTransport
        (fun {n : BHist} _nUnary => hsame_refl (s n))
        (fun {n : BHist} _nUnary => hsame_refl (M n)) same carrier
  · intro _h source
    exact source
  · intro _h source
    exact source

theorem CompleteMetricLimitWitness_standard_bridge {X : BHist -> Prop}
    {s M : BHist -> BHist} {limit : BHist}
    (carrierTransport : forall {h k : BHist}, hsame h k -> X h -> X k) :
    CompleteMetricLimitWitness X s M limit ->
      SemanticNameCert (CompleteMetricLimitWitness X s M) (CompleteMetricLimitWitness X s M)
        (CompleteMetricLimitWitness X s M) hsame ∧ X limit ∧
        (forall {n : BHist}, UnaryHistory n -> X (s n) ->
          exists d : BHist,
            MetricDistanceWitness (s n) limit d ∧ Cont (s n) limit d ∧
              RatHistoryClassifier d (M n)) := by
  intro witness
  exact And.intro
    (CompleteMetricLimitWitness_name_certificate carrierTransport witness)
    (And.intro witness.left (fun {n : BHist} nUnary source => witness.right nUnary source))

theorem CompleteMetricLimitWitness_metric_budget_shape_lock {X : BHist -> Prop}
    {s M : BHist -> BHist} {limit n : BHist} :
    CompleteMetricLimitWitness X s M limit -> UnaryHistory n -> X (s n) ->
      exists d : BHist,
        MetricDistanceWitness (s n) limit d ∧ Cont (s n) limit d ∧
          RatHistoryClassifier d (M n) ∧ (hsame d BHist.Empty -> False) ∧
            (forall z : BHist, hsame d (BHist.e0 z) -> False) := by
  intro witness nUnary source
  cases witness.right nUnary source with
  | intro d distanceData =>
      have endpointNonempty := RatHistoryClassifier_endpoints_not_empty distanceData.right.right
      have endpointZeroExcluded :
          forall z : BHist, hsame d (BHist.e0 z) -> False := by
        intro z sameZero
        exact (RatHistoryClassifier_e0_endpoint_absurd (tail := z) (d := M n)).left
          (RatHistoryClassifier_hsame_transport sameZero (hsame_refl (M n))
            distanceData.right.right)
      exact ⟨d, distanceData.left, distanceData.right.left, distanceData.right.right,
        endpointNonempty.left, endpointZeroExcluded⟩

theorem CompleteMetricLimitWitness_observation_distance_package
    {X : BHist -> Prop} {s M : BHist -> BHist} {limit n : BHist} :
    CompleteMetricLimitWitness X s M limit -> UnaryHistory n -> X (s n) ->
      exists d : BHist,
        MetricDistanceWitness (s n) limit d ∧
          Cont (s n) limit d ∧ RatHistoryCarrier d ∧ RatHistoryCarrier (M n) ∧
            PositiveUnaryDenominator d ∧ PositiveUnaryDenominator (M n) := by
  intro witness nUnary source
  cases witness.right nUnary source with
  | intro d distanceData =>
      have positives :
          PositiveUnaryDenominator d ∧ PositiveUnaryDenominator (M n) :=
        RatHistoryClassifier_positive_denominators distanceData.right.right
      exact ⟨d, distanceData.left, distanceData.right.left, distanceData.right.right.left,
        distanceData.right.right.right.left, positives.left, positives.right⟩

theorem CompleteMetricLimitWitness_standard_bridge_row_package
    {X : BHist -> Prop} {s M : BHist -> BHist} {limit n : BHist} :
    CompleteMetricLimitWitness X s M limit -> UnaryHistory n -> X (s n) ->
      exists d : BHist,
        MetricDistanceWitness (s n) limit d ∧ Cont (s n) limit d ∧
          RatHistoryClassifier d (M n) ∧ RatHistoryCarrier d ∧ RatHistoryCarrier (M n) := by
  intro witness nUnary source
  cases witness.right nUnary source with
  | intro d distanceData =>
      exact ⟨d, distanceData.left, distanceData.right.left, distanceData.right.right,
        distanceData.right.right.left, distanceData.right.right.right.left⟩

theorem CompleteMetricLimitWitness_observation_distance_deterministic
    {X : BHist -> Prop} {s M : BHist -> BHist} {limit n d' : BHist} :
    CompleteMetricLimitWitness X s M limit -> UnaryHistory n -> X (s n) ->
      MetricDistanceWitness (s n) limit d' ->
        exists d : BHist,
          MetricDistanceWitness (s n) limit d ∧ RatHistoryClassifier d (M n) ∧ hsame d d' := by
  intro witness nUnary source externalDistance
  cases witness.right nUnary source with
  | intro d distanceData =>
      exact ⟨d, distanceData.left, distanceData.right.right,
        cont_deterministic distanceData.right.left externalDistance.right.right.right⟩

theorem SingletonCompleteMetric_laws :
    hsame BHist.Empty BHist.Empty ∧
      (forall {x : BHist}, hsame x BHist.Empty ->
        MetricDistanceWitness x BHist.Empty BHist.Empty) ∧
      (forall {x y : BHist}, hsame x BHist.Empty -> hsame y BHist.Empty -> hsame x y) := by
  constructor
  · exact hsame_refl BHist.Empty
  constructor
  · intro x sameX
    exact
      (MetricDistanceWitness_empty_distance_iff (x := x) (y := BHist.Empty)).mpr
        (And.intro sameX (hsame_refl BHist.Empty))
  · intro x y sameX sameY
    exact hsame_trans sameX (hsame_symm sameY)

theorem CompleteMetricLimitWitness_empty_modulus_observation_metric_row
    {X : BHist -> Prop} {s M : BHist -> BHist} {limit n : BHist} :
    CompleteMetricLimitWitness X s M limit -> UnaryHistory n -> X (s n) ->
      hsame (M n) BHist.Empty -> MetricDistanceWitness (s n) limit BHist.Empty := by
  intro witness nUnary source sameModulus
  cases witness.right nUnary source with
  | intro d distanceData =>
      have sameDistance : hsame d BHist.Empty :=
        hsame_trans distanceData.right.right.right.right sameModulus
      exact MetricDistanceWitness_hsame_fields_transport
        (hsame_refl (s n)) (hsame_refl limit) sameDistance distanceData.left

theorem CompleteMetricLimitWitness_empty_modulus_observation_endpoint
    {X : BHist -> Prop} {s M : BHist -> BHist} {limit n : BHist} :
    CompleteMetricLimitWitness X s M limit -> UnaryHistory n -> X (s n) ->
      hsame (M n) BHist.Empty -> hsame (s n) BHist.Empty ∧ hsame limit BHist.Empty := by
  intro witness nUnary source sameModulus
  exact
    (MetricDistanceWitness_empty_distance_iff (x := s n) (y := limit)).mp
      (CompleteMetricLimitWitness_empty_modulus_observation_metric_row
        witness nUnary source sameModulus)

theorem CompleteMetricLimitWitness_singleton_stream_witness {s M : BHist -> BHist} :
    (forall {n : BHist}, UnaryHistory n -> hsame (s n) BHist.Empty) ->
      (forall {n : BHist}, UnaryHistory n -> RatHistoryClassifier (s n) (M n)) ->
        CompleteMetricLimitWitness (fun h : BHist => hsame h BHist.Empty) s M BHist.Empty := by
  intro streamEmpty ratRow
  constructor
  · exact hsame_refl BHist.Empty
  · intro n nUnary _source
    have sourceUnary : UnaryHistory (s n) :=
      unary_transport unary_empty (hsame_symm (streamEmpty nUnary))
    exact
      Exists.intro (s n)
        (And.intro
          ((MetricDistanceWitness_empty_right_iff (x := s n) (d := s n)).mpr
            (And.intro sourceUnary (hsame_refl (s n))))
          (And.intro (cont_right_unit_iff.mpr (hsame_refl (s n))) (ratRow nUnary)))

theorem CompleteMetricLimitWitness_singleton_distance_rat_readback
    {s M : BHist -> BHist} {n : BHist} :
    CompleteMetricLimitWitness (fun h : BHist => hsame h BHist.Empty) s M BHist.Empty ->
      UnaryHistory n -> hsame (s n) BHist.Empty ->
        exists d : BHist, hsame d (s n) ∧ RatHistoryClassifier d (M n) := by
  intro witness nUnary source
  cases witness.right nUnary source with
  | intro d distanceRow =>
      have boundary :=
        (MetricDistanceWitness_empty_right_iff (x := s n) (d := d)).mp distanceRow.left
      exact Exists.intro d (And.intro boundary.right distanceRow.right.right)

def CompleteMetricSingletonInstance (s M : BHist -> BHist) : Prop :=
  hsame BHist.Empty BHist.Empty ∧
    (forall {n : BHist}, UnaryHistory n -> hsame (s n) BHist.Empty ->
      MetricDistanceWitness (s n) BHist.Empty BHist.Empty ∧
        Cont (s n) BHist.Empty BHist.Empty ∧ RatHistoryClassifier BHist.Empty (M n))

theorem CompleteMetricLimitWitness_singleton_uniqueness
    {s M0 M1 : BHist -> BHist} {l0 l1 : BHist} :
    CompleteMetricLimitWitness (fun h : BHist => hsame h BHist.Empty) s M0 l0 ->
      CompleteMetricLimitWitness (fun h : BHist => hsame h BHist.Empty) s M1 l1 ->
        hsame l0 l1 := by
  intro witness0 witness1
  exact hsame_trans witness0.left (hsame_symm witness1.left)

theorem CompleteMetricLimitWitness_singleton_observation_package
    {s M : BHist -> BHist} {limit n : BHist} :
    CompleteMetricLimitWitness (fun h : BHist => hsame h BHist.Empty) s M limit ->
      UnaryHistory n -> hsame (s n) BHist.Empty ->
        exists d : BHist,
          hsame d BHist.Empty ∧ MetricDistanceWitness (s n) limit d ∧
            Cont (s n) limit d ∧ RatHistoryClassifier d (M n) := by
  intro witness nUnary sourceEmpty
  cases witness.right nUnary sourceEmpty with
  | intro d observation =>
      have limitEmpty : hsame limit BHist.Empty := witness.left
      have sourceLimitEmpty : hsame (append (s n) limit) BHist.Empty := by
        exact hsame_trans (congrArg (fun source => append source limit) sourceEmpty)
          (hsame_trans (append_empty_left limit) limitEmpty)
      have distanceEmpty : hsame d BHist.Empty :=
        hsame_trans observation.right.left sourceLimitEmpty
      exact Exists.intro d
        (And.intro distanceEmpty
          (And.intro observation.left
            (And.intro observation.right.left observation.right.right)))

theorem CompleteMetricLimitWitness_singleton_observation_empty_distance
    {s M : BHist -> BHist} {n : BHist} :
    CompleteMetricLimitWitness (fun h : BHist => hsame h BHist.Empty) s M BHist.Empty ->
      UnaryHistory n -> hsame (s n) BHist.Empty ->
        exists d : BHist,
          MetricDistanceWitness (s n) BHist.Empty d ∧ Cont (s n) BHist.Empty d ∧
            RatHistoryClassifier d (M n) ∧ hsame d BHist.Empty := by
  intro witness nUnary sourceEmpty
  cases witness.right nUnary sourceEmpty with
  | intro d distanceData =>
      have distanceEmpty : hsame d (s n) :=
        cont_right_unit_result distanceData.right.left
      have dEmpty : hsame d BHist.Empty :=
        hsame_trans distanceEmpty sourceEmpty
      exact ⟨d, distanceData.left, distanceData.right.left, distanceData.right.right, dEmpty⟩

theorem CompleteMetricSingletonLimitSelector_visible_context_metric {s : BHist -> BHist}
    {p q n : BHist} :
    UnaryHistory p -> UnaryHistory q -> UnaryHistory n -> hsame (s n) BHist.Empty ->
      MetricDistanceWitness (append p (s n)) (append BHist.Empty q)
          (append (append p BHist.Empty) q) ∧
        Cont (append p (s n)) q (append (append p BHist.Empty) q) := by
  intro pUnary qUnary _nUnary sourceEmpty
  constructor
  · exact
      (MetricDistanceWitness_visible_context_empty_distance_iff (p := p) (q := q)
        (x := s n) (y := BHist.Empty)).mpr
        ⟨pUnary, qUnary, sourceEmpty, hsame_refl BHist.Empty⟩
  · exact
      cont_intro (congrArg (fun x : BHist => append (append p x) q)
        (hsame_symm sourceEmpty))

theorem CompleteMetricLimitWitness_row_result_alignment {X : BHist -> Prop}
    {s M : BHist -> BHist} {limit n d e : BHist} :
    CompleteMetricLimitWitness X s M limit -> UnaryHistory n -> X (s n) ->
      MetricDistanceWitness (s n) limit e -> Cont (s n) limit d ->
        RatHistoryClassifier d (M n) ->
          hsame d e ∧ RatHistoryClassifier e (M n) := by
  intro witness nUnary source rowMetric rowCont rowRat
  cases witness.right nUnary source with
  | intro witnessDistance witnessData =>
      have sameMetric : hsame witnessDistance e :=
        MetricDistanceWitness_hsame_result_deterministic (hsame_refl (s n))
          (hsame_refl limit) witnessData.left rowMetric
      have sameCont : hsame d witnessDistance :=
        cont_deterministic rowCont witnessData.right.left
      have sameDE : hsame d e := hsame_trans sameCont sameMetric
      exact ⟨sameDE,
        RatHistoryClassifier_hsame_transport sameDE (hsame_refl (M n)) rowRat⟩

theorem CompleteMetricLimitWitness_singleton_classifier_distance
    {s M0 M1 : BHist -> BHist} {l0 l1 : BHist} :
    CompleteMetricLimitWitness (fun h : BHist => hsame h BHist.Empty) s M0 l0 ->
      CompleteMetricLimitWitness (fun h : BHist => hsame h BHist.Empty) s M1 l1 ->
        hsame l0 l1 ∧ MetricDistanceWitness l0 l1 BHist.Empty := by
  intro witness0 witness1
  have sameLimits : hsame l0 l1 :=
    CompleteMetricLimitWitness_singleton_uniqueness witness0 witness1
  have distance : MetricDistanceWitness l0 l1 BHist.Empty :=
    (MetricDistanceWitness_empty_distance_iff (x := l0) (y := l1)).mpr
      (And.intro witness0.left witness1.left)
  exact And.intro sameLimits distance

def CompleteMetricSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

theorem CompleteMetricSingletonCarrier_empty_distance {x : BHist} :
    CompleteMetricSingletonCarrier x -> MetricDistanceWitness x BHist.Empty BHist.Empty := by
  intro carrier
  exact
    (MetricDistanceWitness_empty_distance_iff (x := x) (y := BHist.Empty)).mpr
      (And.intro carrier (hsame_refl BHist.Empty))

def CompleteMetricSingletonClassifier (h k : BHist) : Prop :=
  CompleteMetricSingletonCarrier h ∧ CompleteMetricSingletonCarrier k ∧ hsame h k

theorem CompleteMetricSingleton_semantic_name_certificate :
    SemanticNameCert CompleteMetricSingletonCarrier CompleteMetricSingletonCarrier
      CompleteMetricSingletonCarrier CompleteMetricSingletonClassifier := by
  have emptyCarrier : CompleteMetricSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
      equiv_refl := by
        intro h carrier
        exact And.intro carrier (And.intro carrier (hsame_refl h))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro h k classified _carrier
        exact classified.right.left
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

end BEDC.Derived.CompleteMetricUp
