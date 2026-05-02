import BEDC.Derived.RatUp

namespace BEDC.Derived.RatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RatHistoryCarrier_e0_absurd {tail : BEDC.FKernel.Hist.BHist} :
    RatHistoryCarrier (BEDC.FKernel.Hist.BHist.e0 tail) -> False := by
  intro carrier
  cases carrier with
  | intro _ signData =>
      cases signData with
      | intro _ ratCarrier =>
          exact PositiveUnaryDenominator_e0_absurd
            (RatCarrier_positive_denominator ratCarrier)

theorem RatHistoryCarrier_e1_tail_unary_iff {tail : BHist} :
    RatHistoryCarrier (BHist.e1 tail) ↔ UnaryHistory tail := by
  constructor
  · intro carrier
    have positive : PositiveUnaryDenominator (BHist.e1 tail) :=
      RatHistoryCarrier_iff_positive_denominator.mp carrier
    exact PositiveUnaryDenominator_e1_iff_unary.mp positive
  · intro tailUnary
    have positive : PositiveUnaryDenominator (BHist.e1 tail) :=
      PositiveUnaryDenominator_e1_iff_unary.mpr tailUnary
    exact RatHistoryCarrier_iff_positive_denominator.mpr positive

theorem RatHistoryClassifier_e1_tail_unary_iff {d e : BHist} :
    RatHistoryClassifier (BHist.e1 d) (BHist.e1 e) ↔
      UnaryHistory d ∧ UnaryHistory e ∧ hsame d e := by
  constructor
  · intro classifier
    cases classifier with
    | intro carrierD rest =>
        cases rest with
        | intro carrierE sameDE =>
            exact ⟨RatHistoryCarrier_e1_tail_unary_iff.mp carrierD,
              RatHistoryCarrier_e1_tail_unary_iff.mp carrierE,
                hsame_e1_iff.mp sameDE⟩
  · intro data
    cases data with
    | intro unaryD rest =>
        cases rest with
        | intro unaryE sameDE =>
            exact ⟨RatHistoryCarrier_e1_tail_unary_iff.mpr unaryD,
              RatHistoryCarrier_e1_tail_unary_iff.mpr unaryE,
                hsame_e1_congr sameDE⟩

theorem RatHistoryClassifier_positive_denominators {d e : BEDC.FKernel.Hist.BHist} :
    RatHistoryClassifier d e → PositiveUnaryDenominator d ∧ PositiveUnaryDenominator e := by
  intro classifier
  cases classifier with
  | intro carrierD rest =>
      cases rest with
      | intro carrierE _sameDE =>
          exact ⟨RatHistoryCarrier_iff_positive_denominator.mp carrierD,
            RatHistoryCarrier_iff_positive_denominator.mp carrierE⟩

theorem RatHistoryClassifier_endpoints_not_empty {d e : BHist} :
    RatHistoryClassifier d e →
      (hsame d BHist.Empty → False) ∧ (hsame e BHist.Empty → False) := by
  intro classifier
  cases classifier with
  | intro carrierD rest =>
      cases rest with
      | intro carrierE _sameDE =>
          constructor
          · intro sameEmpty
            exact RatHistoryCarrier_not_empty carrierD sameEmpty
          · intro sameEmpty
            exact RatHistoryCarrier_not_empty carrierE sameEmpty

theorem RatHistoryClassifier_append_unary_denominator_closed {d e tailD tailE : BHist} :
    RatHistoryClassifier d e -> UnaryHistory tailD -> hsame tailD tailE ->
      RatHistoryClassifier (BEDC.FKernel.Cont.append d tailD)
        (BEDC.FKernel.Cont.append e tailE) := by
  intro classifier tailDUnary tailSame
  cases classifier with
  | intro carrierD rest =>
      cases rest with
      | intro carrierE denSame =>
          have tailEUnary : UnaryHistory tailE := unary_transport tailDUnary tailSame
          have carrierDApp :
              RatHistoryCarrier (BEDC.FKernel.Cont.append d tailD) :=
            RatHistoryCarrier_append_unary_denominator_closed carrierD tailDUnary
          have carrierEApp :
              RatHistoryCarrier (BEDC.FKernel.Cont.append e tailE) :=
            RatHistoryCarrier_append_unary_denominator_closed carrierE tailEUnary
          have appendedSame :
              hsame (BEDC.FKernel.Cont.append d tailD)
                (BEDC.FKernel.Cont.append e tailE) := by
            cases denSame
            cases tailSame
            exact hsame_refl (BEDC.FKernel.Cont.append d tailD)
          exact ⟨carrierDApp, carrierEApp, appendedSame⟩

theorem RatHistoryLedgerPolicy_append_unary_denominator_closed
    {raw visible tailRaw tailVisible : BHist} :
    RatHistoryLedgerPolicy raw visible → UnaryHistory tailRaw → hsame tailRaw tailVisible →
      RatHistoryLedgerPolicy (BEDC.FKernel.Cont.append raw tailRaw)
        (BEDC.FKernel.Cont.append visible tailVisible) := by
  intro ledger tailRawUnary tailSame
  cases ledger with
  | intro rawCarrier rawVisibleSame =>
      constructor
      · exact RatHistoryCarrier_append_unary_denominator_closed rawCarrier tailRawUnary
      · cases rawVisibleSame
        cases tailSame
        exact hsame_refl (BEDC.FKernel.Cont.append raw tailRaw)

theorem RatHistoryLedgerPolicy_prepend_unary_denominator_closed
    {raw visible prefRaw prefVisible : BHist} :
    RatHistoryLedgerPolicy raw visible -> UnaryHistory prefRaw -> hsame prefRaw prefVisible ->
      RatHistoryLedgerPolicy (BEDC.FKernel.Cont.append prefRaw raw)
        (BEDC.FKernel.Cont.append prefVisible visible) := by
  intro ledger prefRawUnary prefSame
  cases ledger with
  | intro rawCarrier rawVisibleSame =>
      constructor
      · exact RatHistoryCarrier_prepend_unary_denominator_closed prefRawUnary rawCarrier
      · cases prefSame
        cases rawVisibleSame
        exact hsame_refl (BEDC.FKernel.Cont.append prefRaw raw)

theorem RatHistoryClassifier_prepend_unary_denominator_closed {d e prefD prefE : BHist} :
    RatHistoryClassifier d e -> UnaryHistory prefD -> hsame prefD prefE ->
      RatHistoryClassifier (BEDC.FKernel.Cont.append prefD d)
        (BEDC.FKernel.Cont.append prefE e) := by
  intro classifier prefDUnary prefSame
  cases classifier with
  | intro carrierD rest =>
      cases rest with
      | intro carrierE denSame =>
          have prefEUnary : UnaryHistory prefE := unary_transport prefDUnary prefSame
          have carrierDPre :
              RatHistoryCarrier (BEDC.FKernel.Cont.append prefD d) :=
            RatHistoryCarrier_prepend_unary_denominator_closed prefDUnary carrierD
          have carrierEPre :
              RatHistoryCarrier (BEDC.FKernel.Cont.append prefE e) :=
            RatHistoryCarrier_prepend_unary_denominator_closed prefEUnary carrierE
          have prependedSame :
              hsame (BEDC.FKernel.Cont.append prefD d)
                (BEDC.FKernel.Cont.append prefE e) := by
            cases prefSame
            cases denSame
            exact hsame_refl (BEDC.FKernel.Cont.append prefD d)
          exact ⟨carrierDPre, carrierEPre, prependedSame⟩

theorem RatHistoryClassifier_unary_denominator_context_closed
    {d e prefD prefE tailD tailE : BHist} :
    RatHistoryClassifier d e -> UnaryHistory prefD -> hsame prefD prefE ->
      UnaryHistory tailD -> hsame tailD tailE ->
        RatHistoryClassifier
          (BEDC.FKernel.Cont.append prefD (BEDC.FKernel.Cont.append d tailD))
          (BEDC.FKernel.Cont.append prefE (BEDC.FKernel.Cont.append e tailE)) := by
  intro classifier prefDUnary prefSame tailDUnary tailSame
  have tailClosed :
      RatHistoryClassifier (BEDC.FKernel.Cont.append d tailD)
        (BEDC.FKernel.Cont.append e tailE) :=
    RatHistoryClassifier_append_unary_denominator_closed classifier tailDUnary tailSame
  exact RatHistoryClassifier_prepend_unary_denominator_closed tailClosed prefDUnary prefSame

theorem RatHistoryClassifier_unary_context_e1_pair_readback
    {d e prefD prefE tailD tailE leftTail rightTail : BHist} :
    RatHistoryClassifier d e -> UnaryHistory prefD -> hsame prefD prefE ->
      UnaryHistory tailD -> hsame tailD tailE ->
        hsame (BEDC.FKernel.Cont.append prefD (BEDC.FKernel.Cont.append d tailD))
          (BHist.e1 leftTail) ->
            hsame (BEDC.FKernel.Cont.append prefE (BEDC.FKernel.Cont.append e tailE))
              (BHist.e1 rightTail) ->
                And (UnaryHistory leftTail)
                  (And (UnaryHistory rightTail) (hsame leftTail rightTail)) := by
  intro classifier prefUnary prefSame tailUnary tailSame sameLeft sameRight
  have contextClassifier :=
    RatHistoryClassifier_unary_denominator_context_closed
      classifier prefUnary prefSame tailUnary tailSame
  have displayed :=
    RatHistoryClassifier_hsame_transport sameLeft sameRight contextClassifier
  exact RatHistoryClassifier_e1_tail_unary_iff.mp displayed

theorem RatHistoryLedgerPolicy_classifier_endpoint_equivalence {rho v w : BHist} :
    RatHistoryLedgerPolicy rho v ->
      (RatHistoryClassifier rho w <-> RatHistoryClassifier v w) := by
  intro ledger
  constructor
  · intro classified
    exact RatHistoryClassifier_trans
      (RatHistoryClassifier_symm (RatHistoryLedgerPolicy_raw_visible_classifier ledger))
      classified
  · intro classified
    exact RatHistoryLedgerPolicy_classifier_extension ledger classified

theorem RatHistoryLedgerPolicy_shared_raw_visible_classifier {raw visible visible' : BHist} :
    RatHistoryLedgerPolicy raw visible ->
      RatHistoryLedgerPolicy raw visible' ->
        RatHistoryClassifier visible visible' := by
  intro leftLedger rightLedger
  exact RatHistoryClassifier_trans
    (RatHistoryClassifier_symm (RatHistoryLedgerPolicy_raw_visible_classifier leftLedger))
    (RatHistoryLedgerPolicy_raw_visible_classifier rightLedger)

theorem RatHistoryLedgerPolicy_visible_positive_denominator_readback
    {raw visible tail : BHist} :
    RatHistoryLedgerPolicy raw visible → hsame visible (BHist.e1 tail) → UnaryHistory tail := by
  intro ledger sameVisible
  have visibleCarrier : RatHistoryCarrier visible :=
    RatHistoryLedgerPolicy_visible_carrier ledger
  have displayedCarrier : RatHistoryCarrier (BHist.e1 tail) :=
    RatHistoryCarrier_hsame_transport sameVisible visibleCarrier
  exact RatHistoryCarrier_e1_tail_unary_iff.mp displayedCarrier

end BEDC.Derived.RatUp
