import BEDC.Derived.RatUp.HistoryClassifier

namespace BEDC.Derived.RatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem PositiveUnaryDenominator_append_unary_context {pref den tail : BHist} :
    UnaryHistory pref → PositiveUnaryDenominator den → UnaryHistory tail →
      PositiveUnaryDenominator
        (BEDC.FKernel.Cont.append pref (BEDC.FKernel.Cont.append den tail)) := by
  intro prefUnary positive tailUnary
  exact PositiveUnaryDenominator_append_unary_prefix prefUnary
    (PositiveUnaryDenominator_append_unary_tail positive tailUnary)

theorem PositiveUnaryDenominator_append_unary_left_split {pref den : BHist} :
    UnaryHistory pref -> PositiveUnaryDenominator (BEDC.FKernel.Cont.append pref den) ->
      PositiveUnaryDenominator pref ∨ PositiveUnaryDenominator den := by
  intro prefUnary positive
  cases pref with
  | Empty =>
      exact Or.inr (PositiveUnaryDenominator_hsame_transport (append_empty_left den) positive)
  | e0 prefTail =>
      exact False.elim (unary_no_zero_extension prefUnary)
  | e1 prefTail =>
      exact Or.inl (PositiveUnaryDenominator_e1_iff_unary.mpr
        (unary_e1_inversion prefUnary))

theorem RatCarrier_unary_denominator_context_closed {sign : BMark}
    {numerator denominator pref tail : BHist} :
    UnaryHistory pref -> RatCarrier sign numerator denominator -> UnaryHistory tail ->
      RatCarrier sign numerator
        (BEDC.FKernel.Cont.append pref (BEDC.FKernel.Cont.append denominator tail)) := by
  intro prefUnary carrier tailUnary
  exact RatCarrier_prepend_unary_denominator_closed prefUnary
    (RatCarrier_append_unary_denominator_closed carrier tailUnary)

theorem RatHistoryCarrier_unary_denominator_context_closed {d pref tail : BHist} :
    UnaryHistory pref → RatHistoryCarrier d → UnaryHistory tail →
      RatHistoryCarrier (BEDC.FKernel.Cont.append pref (BEDC.FKernel.Cont.append d tail)) := by
  intro prefUnary carrier tailUnary
  cases carrier with
  | intro sign signData =>
      cases signData with
      | intro numerator ratCarrier =>
          exact
            ⟨sign, numerator,
              RatCarrier_unary_denominator_context_closed prefUnary ratCarrier tailUnary⟩

theorem RatClassifierSpec_append_unary_denominator_context_closed {s1 s2 : BMark}
    {n1 n2 d1 d2 pref1 pref2 tail1 tail2 : BHist} :
    RatClassifierSpec s1 n1 d1 s2 n2 d2 -> UnaryHistory pref1 -> hsame pref1 pref2 ->
      UnaryHistory tail1 -> hsame tail1 tail2 ->
        RatClassifierSpec s1 n1
          (BEDC.FKernel.Cont.append pref1 (BEDC.FKernel.Cont.append d1 tail1))
          s2 n2
          (BEDC.FKernel.Cont.append pref2 (BEDC.FKernel.Cont.append d2 tail2)) := by
  intro classifier pref1Unary samePref tail1Unary sameTail
  exact
    RatClassifierSpec_prepend_unary_denominators_closed
      (RatClassifierSpec_append_unary_denominators_closed classifier tail1Unary sameTail)
      pref1Unary samePref

theorem RatClassifierSpec_append_unary_prefix_denominator_split {s1 s2 : BMark}
    {n1 n2 pref1 pref2 d1 d2 : BHist} :
    RatClassifierSpec s1 n1 (BEDC.FKernel.Cont.append pref1 d1)
        s2 n2 (BEDC.FKernel.Cont.append pref2 d2) ->
      UnaryHistory pref1 -> hsame pref1 pref2 ->
        (PositiveUnaryDenominator pref1 ∨ PositiveUnaryDenominator d1) ∧
          (PositiveUnaryDenominator pref2 ∨ PositiveUnaryDenominator d2) := by
  intro classifier pref1Unary samePref
  have pref2Unary : UnaryHistory pref2 := unary_transport pref1Unary samePref
  have positiveDenominators := RatClassifierSpec_positive_denominators classifier
  constructor
  · exact PositiveUnaryDenominator_append_unary_left_split pref1Unary positiveDenominators.left
  · exact PositiveUnaryDenominator_append_unary_left_split pref2Unary positiveDenominators.right

theorem RatHistoryLedgerPolicy_unary_denominator_context_closed
    {raw visible prefRaw prefVisible tailRaw tailVisible : BHist} :
    RatHistoryLedgerPolicy raw visible -> UnaryHistory prefRaw -> hsame prefRaw prefVisible ->
      UnaryHistory tailRaw -> hsame tailRaw tailVisible ->
        RatHistoryLedgerPolicy
          (BEDC.FKernel.Cont.append prefRaw (BEDC.FKernel.Cont.append raw tailRaw))
          (BEDC.FKernel.Cont.append prefVisible (BEDC.FKernel.Cont.append visible tailVisible)) := by
  intro ledger prefRawUnary samePref tailRawUnary sameTail
  have appended :
      RatHistoryLedgerPolicy (BEDC.FKernel.Cont.append raw tailRaw)
        (BEDC.FKernel.Cont.append visible tailVisible) :=
    RatHistoryLedgerPolicy_append_unary_denominator_closed ledger tailRawUnary sameTail
  exact RatHistoryLedgerPolicy_prepend_unary_denominator_closed appended prefRawUnary samePref

theorem RatHistoryLedgerPolicy_unary_context_zero_extension_endpoint_exclusion
    {raw visible prefRaw prefVisible tailRaw tailVisible z z' : BHist} :
    RatHistoryLedgerPolicy raw visible -> UnaryHistory prefRaw -> hsame prefRaw prefVisible ->
      UnaryHistory tailRaw -> hsame tailRaw tailVisible ->
        (hsame (append prefRaw (append raw tailRaw)) (BHist.e0 z) -> False) ∧
          (hsame (append prefVisible (append visible tailVisible)) (BHist.e0 z') ->
            False) := by
  intro ledger prefRawUnary samePref tailRawUnary sameTail
  have contextLedger :
      RatHistoryLedgerPolicy (append prefRaw (append raw tailRaw))
        (append prefVisible (append visible tailVisible)) :=
    RatHistoryLedgerPolicy_unary_denominator_context_closed ledger prefRawUnary samePref
      tailRawUnary sameTail
  have contextClassifier :
      RatHistoryClassifier (append prefRaw (append raw tailRaw))
        (append prefVisible (append visible tailVisible)) :=
    RatHistoryLedgerPolicy_raw_visible_classifier contextLedger
  constructor
  · intro sameRawZero
    have displayed :
        RatHistoryClassifier (BHist.e0 z)
          (append prefVisible (append visible tailVisible)) :=
      RatHistoryClassifier_hsame_transport sameRawZero
        (hsame_refl (append prefVisible (append visible tailVisible))) contextClassifier
    exact (RatHistoryClassifier_zero_extension_endpoint_exclusion (tail := z)
      (d := append prefVisible (append visible tailVisible))).left displayed
  · intro sameVisibleZero
    have displayed :
        RatHistoryClassifier (append prefRaw (append raw tailRaw)) (BHist.e0 z') :=
      RatHistoryClassifier_hsame_transport
        (hsame_refl (append prefRaw (append raw tailRaw))) sameVisibleZero contextClassifier
    exact (RatHistoryClassifier_zero_extension_endpoint_exclusion (tail := z')
      (d := append prefRaw (append raw tailRaw))).right displayed

theorem RatHistoryClassifier_unary_denominator_context_positive_denominators
    {d e prefD prefE tailD tailE : BHist} :
    RatHistoryClassifier d e -> UnaryHistory prefD -> hsame prefD prefE ->
      UnaryHistory tailD -> hsame tailD tailE ->
        PositiveUnaryDenominator (append prefD (append d tailD)) ∧
          PositiveUnaryDenominator (append prefE (append e tailE)) := by
  intro classified prefUnary samePref tailUnary sameTail
  have contextClassified :
      RatHistoryClassifier (append prefD (append d tailD))
        (append prefE (append e tailE)) :=
    RatHistoryClassifier_unary_denominator_context_closed classified prefUnary samePref
      tailUnary sameTail
  exact RatHistoryClassifier_positive_denominators contextClassified

theorem RatHistoryClassifier_cont_unary_context_positive_denominators
    {d e prefD prefE tailD tailE midD midE outD outE : BHist} :
    RatHistoryClassifier d e -> UnaryHistory prefD -> UnaryHistory tailD ->
      hsame prefD prefE -> hsame tailD tailE -> Cont prefD d midD ->
        Cont midD tailD outD -> Cont prefE e midE -> Cont midE tailE outE ->
          PositiveUnaryDenominator outD ∧ PositiveUnaryDenominator outE := by
  intro classified prefUnary tailUnary samePref sameTail prefDCont outDCont prefECont
    outECont
  have contextClassified :
      RatHistoryClassifier (append prefD (append d tailD))
        (append prefE (append e tailE)) :=
    RatHistoryClassifier_unary_denominator_context_closed classified prefUnary samePref
      tailUnary sameTail
  have sameOutD : hsame (append prefD (append d tailD)) outD := by
    have outEq : outD = append (append prefD d) tailD :=
      Eq.trans outDCont (congrArg (fun h : BHist => append h tailD) prefDCont)
    exact hsame_trans (hsame_symm (append_assoc prefD d tailD)) outEq.symm
  have sameOutE : hsame (append prefE (append e tailE)) outE := by
    have outEq : outE = append (append prefE e) tailE :=
      Eq.trans outECont (congrArg (fun h : BHist => append h tailE) prefECont)
    exact hsame_trans (hsame_symm (append_assoc prefE e tailE)) outEq.symm
  exact RatHistoryClassifier_positive_denominators
    (RatHistoryClassifier_hsame_transport sameOutD sameOutE contextClassified)

theorem RatHistoryLedgerPolicy_cont_unary_context_positive_denominators
    {raw visible prefRaw prefVisible tailRaw tailVisible midRaw midVisible
      outRaw outVisible : BHist} :
    RatHistoryLedgerPolicy raw visible -> UnaryHistory prefRaw -> hsame prefRaw prefVisible ->
      UnaryHistory tailRaw -> hsame tailRaw tailVisible -> Cont prefRaw raw midRaw ->
        Cont midRaw tailRaw outRaw -> Cont prefVisible visible midVisible ->
          Cont midVisible tailVisible outVisible ->
            PositiveUnaryDenominator outRaw ∧ PositiveUnaryDenominator outVisible := by
  intro ledger prefUnary samePref tailUnary sameTail prefRawCont outRawCont prefVisibleCont
    outVisibleCont
  have contextLedger :
      RatHistoryLedgerPolicy (append prefRaw (append raw tailRaw))
        (append prefVisible (append visible tailVisible)) :=
    RatHistoryLedgerPolicy_unary_denominator_context_closed ledger prefUnary samePref
      tailUnary sameTail
  have sameOutRaw : hsame (append prefRaw (append raw tailRaw)) outRaw := by
    have outEq : outRaw = append (append prefRaw raw) tailRaw :=
      Eq.trans outRawCont (congrArg (fun h : BHist => append h tailRaw) prefRawCont)
    exact hsame_trans (hsame_symm (append_assoc prefRaw raw tailRaw)) outEq.symm
  have sameOutVisible : hsame (append prefVisible (append visible tailVisible)) outVisible := by
    have outEq : outVisible = append (append prefVisible visible) tailVisible :=
      Eq.trans outVisibleCont
        (congrArg (fun h : BHist => append h tailVisible) prefVisibleCont)
    exact hsame_trans (hsame_symm (append_assoc prefVisible visible tailVisible)) outEq.symm
  have displayedLedger : RatHistoryLedgerPolicy outRaw outVisible :=
    RatHistoryLedgerPolicy_hsame_transport contextLedger sameOutRaw sameOutVisible
  constructor
  · exact RatHistoryCarrier_iff_positive_denominator.mp displayedLedger.left
  · exact RatHistoryCarrier_iff_positive_denominator.mp
      (RatHistoryLedgerPolicy_visible_carrier displayedLedger)

theorem RatHistoryLedgerPolicy_shared_raw_contextual_visible_classifier
    {raw visible visible' prefRaw prefVisible prefVisible' tailRaw tailVisible
      tailVisible' : BHist} :
    RatHistoryLedgerPolicy raw visible -> RatHistoryLedgerPolicy raw visible' ->
      UnaryHistory prefRaw -> hsame prefRaw prefVisible -> hsame prefRaw prefVisible' ->
        UnaryHistory tailRaw -> hsame tailRaw tailVisible -> hsame tailRaw tailVisible' ->
          RatHistoryClassifier (append prefVisible (append visible tailVisible))
            (append prefVisible' (append visible' tailVisible')) := by
  intro leftLedger rightLedger prefUnary samePref samePref' tailUnary sameTail sameTail'
  have leftContextLedger :
      RatHistoryLedgerPolicy (append prefRaw (append raw tailRaw))
        (append prefVisible (append visible tailVisible)) :=
    RatHistoryLedgerPolicy_unary_denominator_context_closed leftLedger prefUnary samePref
      tailUnary sameTail
  have rightContextLedger :
      RatHistoryLedgerPolicy (append prefRaw (append raw tailRaw))
        (append prefVisible' (append visible' tailVisible')) :=
      RatHistoryLedgerPolicy_unary_denominator_context_closed rightLedger prefUnary samePref'
      tailUnary sameTail'
  exact RatHistoryLedgerPolicy_shared_raw_visible_classifier leftContextLedger rightContextLedger

theorem RatHistoryLedgerPolicy_shared_raw_context_visible_classifier
    {raw visible visible' prefRaw prefVisible prefVisible' tailRaw tailVisible
      tailVisible' : BHist} :
    RatHistoryLedgerPolicy raw visible -> RatHistoryLedgerPolicy raw visible' ->
      UnaryHistory prefRaw -> hsame prefRaw prefVisible -> hsame prefRaw prefVisible' ->
        UnaryHistory tailRaw -> hsame tailRaw tailVisible -> hsame tailRaw tailVisible' ->
          RatHistoryClassifier (append prefVisible (append visible tailVisible))
            (append prefVisible' (append visible' tailVisible')) := by
  intro leftLedger rightLedger prefRawUnary samePrefVisible samePrefVisible' tailRawUnary
    sameTailVisible sameTailVisible'
  have leftContext :
      RatHistoryLedgerPolicy (append prefRaw (append raw tailRaw))
        (append prefVisible (append visible tailVisible)) :=
    RatHistoryLedgerPolicy_unary_denominator_context_closed leftLedger prefRawUnary
      samePrefVisible tailRawUnary sameTailVisible
  have rightContext :
      RatHistoryLedgerPolicy (append prefRaw (append raw tailRaw))
        (append prefVisible' (append visible' tailVisible')) :=
    RatHistoryLedgerPolicy_unary_denominator_context_closed rightLedger prefRawUnary
      samePrefVisible' tailRawUnary sameTailVisible'
  exact RatHistoryLedgerPolicy_shared_raw_visible_classifier leftContext rightContext

theorem RatHistoryLedgerPolicy_shared_raw_context_e1_pair_readback
    {raw visible visible' prefRaw prefVisible prefVisible' tailRaw tailVisible tailVisible'
      leftTail rightTail : BHist} :
    RatHistoryLedgerPolicy raw visible -> RatHistoryLedgerPolicy raw visible' ->
      UnaryHistory prefRaw -> hsame prefRaw prefVisible -> hsame prefRaw prefVisible' ->
        UnaryHistory tailRaw -> hsame tailRaw tailVisible -> hsame tailRaw tailVisible' ->
          hsame (append prefVisible (append visible tailVisible)) (BHist.e1 leftTail) ->
            hsame (append prefVisible' (append visible' tailVisible')) (BHist.e1 rightTail) ->
              UnaryHistory leftTail ∧ UnaryHistory rightTail ∧ hsame leftTail rightTail := by
  intro leftLedger rightLedger prefRawUnary samePrefVisible samePrefVisible' tailRawUnary
    sameTailVisible sameTailVisible' sameLeft sameRight
  have contextClassifier :
      RatHistoryClassifier (append prefVisible (append visible tailVisible))
        (append prefVisible' (append visible' tailVisible')) :=
    RatHistoryLedgerPolicy_shared_raw_context_visible_classifier leftLedger rightLedger
      prefRawUnary samePrefVisible samePrefVisible' tailRawUnary sameTailVisible
      sameTailVisible'
  have displayed :
      RatHistoryClassifier (BHist.e1 leftTail) (BHist.e1 rightTail) :=
    RatHistoryClassifier_hsame_transport sameLeft sameRight contextClassifier
  exact RatHistoryClassifier_e1_tail_unary_iff.mp displayed

theorem RatHistoryClassifier_unary_context_zero_extension_endpoint_absurd
    {d e prefD prefE tailD tailE leftZero rightZero : BHist} :
    RatHistoryClassifier d e -> UnaryHistory prefD -> hsame prefD prefE ->
      UnaryHistory tailD -> hsame tailD tailE ->
        (hsame (append prefD (append d tailD)) (BHist.e0 leftZero) -> False) ∧
          (hsame (append prefE (append e tailE)) (BHist.e0 rightZero) -> False) := by
  intro classified prefUnary samePref tailUnary sameTail
  have positiveDenominators :=
    RatHistoryClassifier_unary_denominator_context_positive_denominators classified
      prefUnary samePref tailUnary sameTail
  constructor
  · intro sameLeft
    exact PositiveUnaryDenominator_e0_absurd
      (PositiveUnaryDenominator_hsame_transport sameLeft positiveDenominators.left)
  · intro sameRight
    exact PositiveUnaryDenominator_e0_absurd
      (PositiveUnaryDenominator_hsame_transport sameRight positiveDenominators.right)

end BEDC.Derived.RatUp
