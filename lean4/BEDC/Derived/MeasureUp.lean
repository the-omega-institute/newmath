import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MeasureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def MeasureZeroBHistCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def MeasureZeroBHistClassifier (h k : BHist) : Prop :=
  MeasureZeroBHistCarrier h ∧ MeasureZeroBHistCarrier k ∧ hsame h k

theorem MeasureZeroBHist_carrier_classifier_stability
    {h k event endpoint endpoint' : BHist} :
    MeasureZeroBHistCarrier h ->
      MeasureZeroBHistClassifier h k ->
        MeasureZeroBHistClassifier event BHist.Empty ->
          hsame endpoint BHist.Empty ->
            hsame endpoint endpoint' ->
              MeasureZeroBHistCarrier k ∧
                MeasureZeroBHistClassifier event BHist.Empty ∧
                  MeasureZeroBHistClassifier endpoint endpoint' := by
  intro hCarrier classified eventClassified endpointZero sameEndpoint
  have kCarrier : MeasureZeroBHistCarrier k :=
    hsame_trans (hsame_symm classified.right.right) hCarrier
  have endpoint'Zero : MeasureZeroBHistCarrier endpoint' :=
    hsame_trans (hsame_symm sameEndpoint) endpointZero
  have endpointClassified : MeasureZeroBHistClassifier endpoint endpoint' :=
    And.intro endpointZero (And.intro endpoint'Zero sameEndpoint)
  exact And.intro kCarrier (And.intro eventClassified endpointClassified)

theorem MeasureZeroBHist_event_row_coverage {event union value sum : BHist} :
    MeasureZeroBHistClassifier event BHist.Empty ->
      hsame value BHist.Empty ->
        hsame sum BHist.Empty ->
          hsame union BHist.Empty ->
            MeasureZeroBHistClassifier event BHist.Empty ∧
              MeasureZeroBHistClassifier union BHist.Empty ∧
                MeasureZeroBHistClassifier value sum := by
  intro eventClassified valueZero sumZero unionZero
  have unionClassified : MeasureZeroBHistClassifier union BHist.Empty :=
    And.intro unionZero (And.intro (hsame_refl BHist.Empty) unionZero)
  have valueSumSame : hsame value sum :=
    hsame_trans valueZero (hsame_symm sumZero)
  have valueSumClassified : MeasureZeroBHistClassifier value sum :=
    And.intro valueZero (And.intro sumZero valueSumSame)
  exact And.intro eventClassified (And.intro unionClassified valueSumClassified)

theorem MeasureZeroBHist_continuation_endpoint_stability
    {h k event event' endpoint endpoint' : BHist} :
    hsame h BHist.Empty -> hsame h k -> hsame event BHist.Empty ->
      hsame event event' -> Cont BHist.Empty BHist.Empty endpoint ->
        Cont BHist.Empty BHist.Empty endpoint' ->
          hsame k BHist.Empty ∧ hsame event' BHist.Empty ∧ hsame endpoint endpoint' := by
  intro histEmpty sameHist eventEmpty sameEvent endpointCont endpointCont'
  have targetHistEmpty : hsame k BHist.Empty :=
    hsame_trans (hsame_symm sameHist) histEmpty
  have targetEventEmpty : hsame event' BHist.Empty :=
    hsame_trans (hsame_symm sameEvent) eventEmpty
  have endpointsSame : hsame endpoint endpoint' :=
    cont_deterministic endpointCont endpointCont'
  exact And.intro targetHistEmpty (And.intro targetEventEmpty endpointsSame)

theorem MeasureCountableZeroTail_canonical {tail endpoint : BHist} :
    Cont BHist.Empty BHist.Empty tail -> Cont tail BHist.Empty endpoint ->
      hsame tail BHist.Empty ∧ hsame endpoint BHist.Empty ∧ hsame endpoint tail := by
  intro tailCont endpointCont
  have tailEmpty : hsame tail BHist.Empty :=
    cont_left_unit_result tailCont
  have endpointTail : hsame endpoint tail :=
    cont_deterministic endpointCont (cont_right_unit tail)
  have endpointEmpty : hsame endpoint BHist.Empty :=
    hsame_trans endpointTail tailEmpty
  exact And.intro tailEmpty (And.intro endpointEmpty endpointTail)

theorem MeasureZeroBHist_relative_difference_zero_row {h event diff union endpoint : BHist} :
    MeasureZeroBHistCarrier h -> MeasureZeroBHistClassifier event BHist.Empty ->
      MeasureZeroBHistClassifier diff BHist.Empty -> Cont event diff union ->
        hsame endpoint diff ->
          MeasureZeroBHistCarrier diff ∧ MeasureZeroBHistClassifier union BHist.Empty ∧
            hsame endpoint BHist.Empty := by
  intro _histCarrier eventZero diffZero unionCont endpointDiff
  have unionZero : hsame union BHist.Empty :=
    cont_respects_hsame eventZero.left diffZero.left unionCont (cont_left_unit BHist.Empty)
  have unionClassified : MeasureZeroBHistClassifier union BHist.Empty :=
    And.intro unionZero (And.intro (hsame_refl BHist.Empty) unionZero)
  have endpointZero : hsame endpoint BHist.Empty :=
    hsame_trans endpointDiff diffZero.left
  exact And.intro diffZero.left (And.intro unionClassified endpointZero)

theorem MeasureZeroBHist_semantic_name_certificate :
    SemanticNameCert MeasureZeroBHistCarrier MeasureZeroBHistCarrier
      MeasureZeroBHistCarrier MeasureZeroBHistClassifier := by
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty (hsame_refl BHist.Empty)
      equiv_refl := by
        intro h hCarrier
        exact And.intro hCarrier (And.intro hCarrier (hsame_refl h))
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
        intro h k classified _hCarrier
        exact classified.right.left
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

end BEDC.Derived.MeasureUp
