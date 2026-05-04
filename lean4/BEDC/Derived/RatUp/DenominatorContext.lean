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

end BEDC.Derived.RatUp
