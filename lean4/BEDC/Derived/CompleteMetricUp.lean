import BEDC.Derived.MetricUp
import BEDC.Derived.MetricUp.Transport
import BEDC.Derived.RatUp
import BEDC.FKernel.Cont.Units
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

theorem CompleteMetricLimitWitness_singleton_uniqueness
    {s M0 M1 : BHist -> BHist} {l0 l1 : BHist} :
    CompleteMetricLimitWitness (fun h : BHist => hsame h BHist.Empty) s M0 l0 ->
      CompleteMetricLimitWitness (fun h : BHist => hsame h BHist.Empty) s M1 l1 ->
        hsame l0 l1 := by
  intro witness0 witness1
  exact hsame_trans witness0.left (hsame_symm witness1.left)

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

def CompleteMetricSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

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
