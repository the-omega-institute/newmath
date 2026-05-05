import BEDC.Derived.RatUp

namespace BEDC.Derived.RatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

theorem RatHistoryLedgerPolicy_saturated_denominator_shape_package
    {rho v w zrho zv zw : BHist} :
    RatHistoryLedgerPolicy rho v ->
      (RatHistoryClassifier rho w ∨ RatHistoryClassifier v w ∨
        RatHistoryClassifier w rho ∨ RatHistoryClassifier w v) ->
        UnaryHistory rho ∧ UnaryHistory v ∧ UnaryHistory w ∧
          (hsame rho BHist.Empty -> False) ∧ (hsame v BHist.Empty -> False) ∧
            (hsame w BHist.Empty -> False) ∧
              (hsame rho (BHist.e0 zrho) -> False) ∧
                (hsame v (BHist.e0 zv) -> False) ∧
                  (hsame w (BHist.e0 zw) -> False) := by
  intro ledger linked
  have rhoPositive : PositiveUnaryDenominator rho :=
    RatHistoryCarrier_iff_positive_denominator.mp ledger.left
  have vPositive : PositiveUnaryDenominator v :=
    RatHistoryCarrier_iff_positive_denominator.mp
      (RatHistoryLedgerPolicy_visible_carrier ledger)
  have wCarrier : RatHistoryCarrier w := by
    cases linked with
    | inl rhoW =>
        exact rhoW.right.left
    | inr rest =>
        cases rest with
        | inl vW =>
            exact vW.right.left
        | inr rest' =>
            cases rest' with
            | inl wRho =>
                exact wRho.left
            | inr wV =>
                exact wV.left
  have wPositive : PositiveUnaryDenominator w :=
    RatHistoryCarrier_iff_positive_denominator.mp wCarrier
  have rhoRows := PositiveUnaryDenominator_unary_and_nonempty rhoPositive
  have vRows := PositiveUnaryDenominator_unary_and_nonempty vPositive
  have wRows := PositiveUnaryDenominator_unary_and_nonempty wPositive
  exact And.intro rhoRows.left
    (And.intro vRows.left
      (And.intro wRows.left
        (And.intro rhoRows.right
          (And.intro vRows.right
            (And.intro wRows.right
              (And.intro
                (fun sameZero =>
                  PositiveUnaryDenominator_e0_absurd
                    (PositiveUnaryDenominator_hsame_transport sameZero rhoPositive))
                (And.intro
                  (fun sameZero =>
                    PositiveUnaryDenominator_e0_absurd
                      (PositiveUnaryDenominator_hsame_transport sameZero vPositive))
                  (fun sameZero =>
                    PositiveUnaryDenominator_e0_absurd
                      (PositiveUnaryDenominator_hsame_transport sameZero wPositive)))))))))

theorem RatHistoryClassifier_e0_endpoint_absurd {tail d : BHist} :
    (RatHistoryClassifier (BHist.e0 tail) d → False) ∧
      (RatHistoryClassifier d (BHist.e0 tail) → False) := by
  constructor
  · intro classified
    exact PositiveUnaryDenominator_e0_absurd
      (RatHistoryClassifier_positive_denominators classified).left
  · intro classified
    exact PositiveUnaryDenominator_e0_absurd
      (RatHistoryClassifier_positive_denominators classified).right

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

theorem RatHistoryClassifier_cont_unary_context_e1_pair_readback
    {d e prefD prefE tailD tailE midD midE outD outE leftTail rightTail : BHist} :
    RatHistoryClassifier d e -> UnaryHistory prefD -> hsame prefD prefE ->
      UnaryHistory tailD -> hsame tailD tailE -> Cont prefD d midD ->
        Cont midD tailD outD -> Cont prefE e midE -> Cont midE tailE outE ->
          hsame outD (BHist.e1 leftTail) -> hsame outE (BHist.e1 rightTail) ->
            UnaryHistory leftTail ∧ UnaryHistory rightTail ∧ hsame leftTail rightTail := by
  intro classifier prefUnary prefSame tailUnary tailSame prefDCont outDCont prefECont
    outECont sameLeft sameRight
  have sameLeftNormal :
      hsame (append prefD (append d tailD)) (BHist.e1 leftTail) := by
    exact (append_assoc prefD d tailD).symm.trans
      ((outDCont.trans (congrArg (fun r => append r tailD) prefDCont)).symm.trans
        sameLeft)
  have sameRightNormal :
      hsame (append prefE (append e tailE)) (BHist.e1 rightTail) := by
    exact (append_assoc prefE e tailE).symm.trans
      ((outECont.trans (congrArg (fun r => append r tailE) prefECont)).symm.trans
        sameRight)
  exact RatHistoryClassifier_unary_context_e1_pair_readback classifier prefUnary prefSame
    tailUnary tailSame sameLeftNormal sameRightNormal

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

theorem RatHistoryLedgerPolicy_e1_tail_classifier_saturation {rho v t : BHist} :
    RatHistoryLedgerPolicy rho v ->
      (RatHistoryClassifier rho (BHist.e1 t) <-> RatHistoryClassifier v (BHist.e1 t)) ∧
        (RatHistoryClassifier (BHist.e1 t) rho <-> RatHistoryClassifier (BHist.e1 t) v) ∧
          PositiveUnaryDenominator rho ∧ PositiveUnaryDenominator v ∧
            (RatHistoryClassifier v (BHist.e1 t) -> UnaryHistory t) ∧
              (RatHistoryClassifier (BHist.e1 t) v -> UnaryHistory t) := by
  intro ledger
  have forwardFiber :
      RatHistoryClassifier rho (BHist.e1 t) <-> RatHistoryClassifier v (BHist.e1 t) :=
    RatHistoryLedgerPolicy_classifier_endpoint_equivalence ledger
  have reversedFiber :
      RatHistoryClassifier (BHist.e1 t) rho <-> RatHistoryClassifier (BHist.e1 t) v := by
    constructor
    · intro classified
      have rawForward : RatHistoryClassifier rho (BHist.e1 t) :=
        RatHistoryClassifier_symm classified
      exact RatHistoryClassifier_symm (forwardFiber.mp rawForward)
    · intro classified
      have visibleForward : RatHistoryClassifier v (BHist.e1 t) :=
        RatHistoryClassifier_symm classified
      exact RatHistoryClassifier_symm (forwardFiber.mpr visibleForward)
  have endpointPositives :
      PositiveUnaryDenominator rho ∧ PositiveUnaryDenominator v :=
    RatHistoryClassifier_positive_denominators
      (RatHistoryLedgerPolicy_raw_visible_classifier ledger)
  constructor
  · exact forwardFiber
  · constructor
    · exact reversedFiber
    · constructor
      · exact endpointPositives.left
      · constructor
        · exact endpointPositives.right
        · constructor
          · intro classified
            exact PositiveUnaryDenominator_e1_iff_unary.mp
              (RatHistoryClassifier_positive_denominators classified).right
          · intro classified
            exact PositiveUnaryDenominator_e1_iff_unary.mp
              (RatHistoryClassifier_positive_denominators classified).left

theorem RatHistoryLedgerPolicy_one_tail_classifier_saturation {rho v t : BHist} :
    RatHistoryLedgerPolicy rho v ->
      (RatHistoryClassifier rho (BHist.e1 t) <->
        RatHistoryClassifier v (BHist.e1 t)) ∧
        (RatHistoryClassifier (BHist.e1 t) rho <->
          RatHistoryClassifier (BHist.e1 t) v) ∧
          PositiveUnaryDenominator rho ∧ PositiveUnaryDenominator v ∧
            (RatHistoryClassifier v (BHist.e1 t) -> UnaryHistory t) ∧
              (RatHistoryClassifier (BHist.e1 t) v -> UnaryHistory t) := by
  intro ledger
  exact RatHistoryLedgerPolicy_e1_tail_classifier_saturation ledger

theorem RatHistoryLedgerPolicy_one_tail_denominator_shape_readback
    {rho v t zRho zV zT : BHist} :
    RatHistoryLedgerPolicy rho v ->
      (RatHistoryClassifier rho (BHist.e1 t) ∨
        RatHistoryClassifier v (BHist.e1 t) ∨
          RatHistoryClassifier (BHist.e1 t) rho ∨
            RatHistoryClassifier (BHist.e1 t) v) ->
        UnaryHistory rho ∧ UnaryHistory v ∧ UnaryHistory (BHist.e1 t) ∧
          UnaryHistory t ∧
            (hsame rho BHist.Empty -> False) ∧
              (hsame v BHist.Empty -> False) ∧
                (hsame (BHist.e1 t) BHist.Empty -> False) ∧
                  (hsame rho (BHist.e0 zRho) -> False) ∧
                    (hsame v (BHist.e0 zV) -> False) ∧
                      (hsame (BHist.e1 t) (BHist.e0 zT) -> False) := by
  intro ledger linked
  have shape :=
    RatHistoryLedgerPolicy_saturated_denominator_shape_package
      (rho := rho) (v := v) (w := BHist.e1 t)
      (zrho := zRho) (zv := zV) (zw := zT) ledger linked
  have saturation := RatHistoryLedgerPolicy_one_tail_classifier_saturation (t := t) ledger
  have tailUnary : UnaryHistory t := by
    cases linked with
    | inl rhoTail =>
        exact saturation.right.right.right.right.left (saturation.left.mp rhoTail)
    | inr rest =>
        cases rest with
        | inl vTail =>
            exact saturation.right.right.right.right.left vTail
        | inr rest' =>
            cases rest' with
            | inl tailRho =>
                exact saturation.right.right.right.right.right
                  (saturation.right.left.mp tailRho)
            | inr tailV =>
                exact saturation.right.right.right.right.right tailV
  exact And.intro shape.left
    (And.intro shape.right.left
      (And.intro shape.right.right.left
        (And.intro tailUnary
          (And.intro shape.right.right.right.left
            (And.intro shape.right.right.right.right.left
              (And.intro shape.right.right.right.right.right.left
                (And.intro shape.right.right.right.right.right.right.left
                  (And.intro shape.right.right.right.right.right.right.right.left
                    shape.right.right.right.right.right.right.right.right))))))))

theorem RatHistoryLedgerPolicy_classifier_saturation_unary_package {rho v w : BHist} :
    RatHistoryLedgerPolicy rho v ->
      (RatHistoryClassifier rho w ∨ RatHistoryClassifier v w ∨
        RatHistoryClassifier w rho ∨ RatHistoryClassifier w v) ->
        RatHistoryClassifier rho w ∧ RatHistoryClassifier v w ∧
          RatHistoryClassifier w rho ∧ RatHistoryClassifier w v ∧
            PositiveUnaryDenominator rho ∧ PositiveUnaryDenominator v ∧
              PositiveUnaryDenominator w ∧ UnaryHistory rho ∧ UnaryHistory v ∧
                UnaryHistory w := by
  intro ledger linked
  have forwardFiber :
      RatHistoryClassifier rho w <-> RatHistoryClassifier v w :=
    RatHistoryLedgerPolicy_classifier_endpoint_equivalence ledger
  have endpointClassifiers :
      RatHistoryClassifier rho w ∧ RatHistoryClassifier v w ∧
        RatHistoryClassifier w rho ∧ RatHistoryClassifier w v := by
    cases linked with
    | inl rhoW =>
        have vW : RatHistoryClassifier v w := forwardFiber.mp rhoW
        exact ⟨rhoW, vW, RatHistoryClassifier_symm rhoW, RatHistoryClassifier_symm vW⟩
    | inr rest =>
        cases rest with
        | inl vW =>
            have rhoW : RatHistoryClassifier rho w := forwardFiber.mpr vW
            exact ⟨rhoW, vW, RatHistoryClassifier_symm rhoW, RatHistoryClassifier_symm vW⟩
        | inr rest' =>
            cases rest' with
            | inl wRho =>
                have rhoW : RatHistoryClassifier rho w := RatHistoryClassifier_symm wRho
                have vW : RatHistoryClassifier v w := forwardFiber.mp rhoW
                exact ⟨rhoW, vW, wRho, RatHistoryClassifier_symm vW⟩
            | inr wV =>
                have vW : RatHistoryClassifier v w := RatHistoryClassifier_symm wV
                have rhoW : RatHistoryClassifier rho w := forwardFiber.mpr vW
                exact ⟨rhoW, vW, RatHistoryClassifier_symm rhoW, wV⟩
  have rhoW : RatHistoryClassifier rho w := endpointClassifiers.left
  have vW : RatHistoryClassifier v w := endpointClassifiers.right.left
  have rhoPositives : PositiveUnaryDenominator rho ∧ PositiveUnaryDenominator w :=
    RatHistoryClassifier_positive_denominators rhoW
  have vPositives : PositiveUnaryDenominator v ∧ PositiveUnaryDenominator w :=
    RatHistoryClassifier_positive_denominators vW
  exact ⟨rhoW, vW, endpointClassifiers.right.right.left,
    endpointClassifiers.right.right.right, rhoPositives.left, vPositives.left,
      rhoPositives.right, (PositiveUnaryDenominator_unary_and_nonempty rhoPositives.left).left,
        (PositiveUnaryDenominator_unary_and_nonempty vPositives.left).left,
          (PositiveUnaryDenominator_unary_and_nonempty rhoPositives.right).left⟩

theorem RatHistoryLedgerPolicy_shared_raw_visible_classifier {raw visible visible' : BHist} :
    RatHistoryLedgerPolicy raw visible ->
      RatHistoryLedgerPolicy raw visible' ->
        RatHistoryClassifier visible visible' := by
  intro leftLedger rightLedger
  exact RatHistoryClassifier_trans
    (RatHistoryClassifier_symm (RatHistoryLedgerPolicy_raw_visible_classifier leftLedger))
    (RatHistoryLedgerPolicy_raw_visible_classifier rightLedger)

theorem RatHistoryLedgerPolicy_shared_visible_e0_endpoint_absurd
    {raw visible visible' z z' : BHist} :
    RatHistoryLedgerPolicy raw visible -> RatHistoryLedgerPolicy raw visible' ->
      (hsame visible (BHist.e0 z) -> False) ∧
        (hsame visible' (BHist.e0 z') -> False) := by
  intro leftLedger rightLedger
  have classified : RatHistoryClassifier visible visible' :=
    RatHistoryLedgerPolicy_shared_raw_visible_classifier leftLedger rightLedger
  constructor
  · intro sameZero
    have displayed : RatHistoryClassifier (BHist.e0 z) visible' :=
      RatHistoryClassifier_hsame_transport sameZero (hsame_refl visible') classified
    exact (RatHistoryClassifier_zero_extension_endpoint_exclusion (tail := z)
      (d := visible')).left displayed
  · intro sameZero
    have displayed : RatHistoryClassifier visible (BHist.e0 z') :=
      RatHistoryClassifier_hsame_transport (hsame_refl visible) sameZero classified
    exact (RatHistoryClassifier_zero_extension_endpoint_exclusion (tail := z')
      (d := visible)).right displayed

theorem RatHistoryLedgerPolicy_visible_positive_denominator_readback
    {raw visible tail : BHist} :
    RatHistoryLedgerPolicy raw visible → hsame visible (BHist.e1 tail) → UnaryHistory tail := by
  intro ledger sameVisible
  have visibleCarrier : RatHistoryCarrier visible :=
    RatHistoryLedgerPolicy_visible_carrier ledger
  have displayedCarrier : RatHistoryCarrier (BHist.e1 tail) :=
    RatHistoryCarrier_hsame_transport sameVisible visibleCarrier
  exact RatHistoryCarrier_e1_tail_unary_iff.mp displayedCarrier

theorem RatHistoryLedgerPolicy_visible_target_zero_extension_exclusion
    {rho v w z z' : BHist} :
    RatHistoryLedgerPolicy rho v -> RatHistoryClassifier v w ->
      (hsame rho (BHist.e0 z) -> False) ∧ (hsame w (BHist.e0 z') -> False) := by
  intro ledger visibleTarget
  have rawTarget : RatHistoryClassifier rho w :=
    RatHistoryLedgerPolicy_classifier_extension ledger visibleTarget
  constructor
  · intro sameRawZero
    have displayed : RatHistoryClassifier (BHist.e0 z) w :=
      RatHistoryClassifier_hsame_transport sameRawZero (hsame_refl w) rawTarget
    exact (RatHistoryClassifier_zero_extension_endpoint_exclusion (tail := z) (d := w)).left
      displayed
  · intro sameTargetZero
    have displayed : RatHistoryClassifier rho (BHist.e0 z') :=
      RatHistoryClassifier_hsame_transport (hsame_refl rho) sameTargetZero rawTarget
    exact (RatHistoryClassifier_zero_extension_endpoint_exclusion (tail := z') (d := rho)).right
      displayed

theorem RatHistoryLedgerPolicy_visible_target_e1_pair_readback {rho v w a b : BHist} :
    RatHistoryLedgerPolicy rho v -> RatHistoryClassifier v w -> hsame rho (BHist.e1 a) ->
      hsame w (BHist.e1 b) -> UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro ledger visibleTarget sameRaw sameTarget
  have rawTarget : RatHistoryClassifier rho w :=
    RatHistoryLedgerPolicy_classifier_extension ledger visibleTarget
  have displayed : RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) :=
    RatHistoryClassifier_hsame_transport sameRaw sameTarget rawTarget
  exact RatHistoryClassifier_e1_tail_unary_iff.mp displayed

theorem RatHistoryLedgerPolicy_visible_target_positive_nonempty_package {rho v w : BHist} :
    RatHistoryLedgerPolicy rho v -> RatHistoryClassifier v w ->
      PositiveUnaryDenominator rho ∧ PositiveUnaryDenominator v ∧ PositiveUnaryDenominator w ∧
        (hsame rho BHist.Empty -> False) ∧ (hsame v BHist.Empty -> False) ∧
          (hsame w BHist.Empty -> False) := by
  intro ledger visibleTarget
  have rawTarget : RatHistoryClassifier rho w :=
    RatHistoryLedgerPolicy_classifier_extension ledger visibleTarget
  have rawPositives :
      PositiveUnaryDenominator rho ∧ PositiveUnaryDenominator w :=
    RatHistoryClassifier_positive_denominators rawTarget
  have visiblePositives :
      PositiveUnaryDenominator v ∧ PositiveUnaryDenominator w :=
    RatHistoryClassifier_positive_denominators visibleTarget
  have rhoRows := PositiveUnaryDenominator_unary_and_nonempty rawPositives.left
  have vRows := PositiveUnaryDenominator_unary_and_nonempty visiblePositives.left
  have wRows := PositiveUnaryDenominator_unary_and_nonempty rawPositives.right
  exact And.intro rawPositives.left
    (And.intro visiblePositives.left
      (And.intro rawPositives.right
        (And.intro rhoRows.right (And.intro vRows.right wRows.right))))

theorem RatHistoryLedgerPolicy_bidirectional_target_positive_endpoint_package {rho v w : BHist} :
    RatHistoryLedgerPolicy rho v ->
      (RatHistoryClassifier rho w <-> RatHistoryClassifier v w) ∧
        (RatHistoryClassifier w rho <-> RatHistoryClassifier w v) ∧
          (RatHistoryClassifier v w ->
            PositiveUnaryDenominator rho ∧ PositiveUnaryDenominator v ∧ PositiveUnaryDenominator w) ∧
            (RatHistoryClassifier w v ->
              PositiveUnaryDenominator rho ∧ PositiveUnaryDenominator v ∧ PositiveUnaryDenominator w) ∧
              RatHistoryClassifier rho v ∧ hsame (append rho BHist.Empty) v := by
  intro ledger
  have forwardFiber :
      RatHistoryClassifier rho w <-> RatHistoryClassifier v w :=
    RatHistoryLedgerPolicy_classifier_endpoint_equivalence ledger
  have reversedFiber :
      RatHistoryClassifier w rho <-> RatHistoryClassifier w v := by
    constructor
    · intro classified
      have rawForward : RatHistoryClassifier rho w :=
        RatHistoryClassifier_symm classified
      exact RatHistoryClassifier_symm (forwardFiber.mp rawForward)
    · intro classified
      have visibleForward : RatHistoryClassifier v w :=
        RatHistoryClassifier_symm classified
      exact RatHistoryClassifier_symm (forwardFiber.mpr visibleForward)
  have endpointPositivesFromVisible :
      RatHistoryClassifier v w ->
        PositiveUnaryDenominator rho ∧ PositiveUnaryDenominator v ∧ PositiveUnaryDenominator w := by
    intro visibleTarget
    have rawTarget : RatHistoryClassifier rho w :=
      RatHistoryLedgerPolicy_classifier_extension ledger visibleTarget
    have rawPositives : PositiveUnaryDenominator rho ∧ PositiveUnaryDenominator w :=
      RatHistoryClassifier_positive_denominators rawTarget
    have visiblePositives : PositiveUnaryDenominator v ∧ PositiveUnaryDenominator w :=
      RatHistoryClassifier_positive_denominators visibleTarget
    exact ⟨rawPositives.left, visiblePositives.left, rawPositives.right⟩
  have endpointPositivesFromReversed :
      RatHistoryClassifier w v ->
        PositiveUnaryDenominator rho ∧ PositiveUnaryDenominator v ∧ PositiveUnaryDenominator w := by
    intro reversedVisible
    exact endpointPositivesFromVisible (RatHistoryClassifier_symm reversedVisible)
  have rawVisible : RatHistoryClassifier rho v :=
    RatHistoryLedgerPolicy_raw_visible_classifier ledger
  have endpoint : hsame (append rho BHist.Empty) v :=
    hsame_trans (append_empty_right rho) ledger.right
  exact ⟨forwardFiber, reversedFiber, endpointPositivesFromVisible,
    endpointPositivesFromReversed, rawVisible, endpoint⟩

theorem RatHistoryLedgerPolicy_visible_target_e0_endpoint_absurd {rho v w z z' : BHist} :
    RatHistoryLedgerPolicy rho v -> RatHistoryClassifier v w ->
      (hsame rho (BHist.e0 z) -> False) ∧ (hsame w (BHist.e0 z') -> False) := by
  intro ledger classified
  exact RatHistoryLedgerPolicy_visible_target_zero_extension_exclusion ledger classified

end BEDC.Derived.RatUp
