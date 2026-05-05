import BEDC.Derived.MetricUp
import BEDC.Derived.MetricUp.Transport
import BEDC.Derived.RatUp
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

end BEDC.Derived.CompleteMetricUp
