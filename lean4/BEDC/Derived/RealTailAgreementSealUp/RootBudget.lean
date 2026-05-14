import BEDC.Derived.RealTailAgreementSealUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealTailAgreementSealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RealTailAgreementSealCarrier_root_budget_selector_admission
    {R S W D A H C P N limiter tailBudget selectorBudget agreementRead : BHist} :
    UnaryHistory R →
      UnaryHistory limiter →
        UnaryHistory selectorBudget →
          UnaryHistory W →
            UnaryHistory D →
              UnaryHistory A →
                Cont R limiter tailBudget →
                  Cont tailBudget selectorBudget W →
                    Cont W D agreementRead →
                      (∃ packet : RealTailAgreementSealUp,
                        packet = RealTailAgreementSealUp.mk R S W D A H C P N) →
                        UnaryHistory tailBudget ∧ UnaryHistory agreementRead ∧
                          Cont R limiter tailBudget ∧ Cont tailBudget selectorBudget W ∧
                            Cont W D agreementRead ∧ hsame agreementRead (append W D) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro rootUnary limiterUnary selectorUnary windowUnary dyadicUnary _agreementUnary
  intro rootLimiterRoute tailSelectorRoute windowDyadicRoute packet
  obtain ⟨_packet, packetEq⟩ := packet
  cases packetEq
  have tailBudgetUnary : UnaryHistory tailBudget :=
    unary_cont_closed rootUnary limiterUnary rootLimiterRoute
  have agreementReadUnary : UnaryHistory agreementRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicRoute
  constructor
  · exact tailBudgetUnary
  · constructor
    · exact agreementReadUnary
    · constructor
      · exact rootLimiterRoute
      · constructor
        · exact tailSelectorRoute
        · constructor
          · exact windowDyadicRoute
          · exact windowDyadicRoute

theorem RealTailAgreementSealCarrier_root_dyadic_agreement_exactness
    {R S W D A H C P N limiter tailBudget selectorBudget agreementRead finalRead :
      BHist} :
    UnaryHistory R →
      UnaryHistory limiter →
        UnaryHistory selectorBudget →
          UnaryHistory W →
            UnaryHistory D →
              UnaryHistory A →
                Cont R limiter tailBudget →
                  Cont tailBudget selectorBudget W →
                    Cont W D agreementRead →
                      Cont agreementRead A finalRead →
                        (∃ packet : RealTailAgreementSealUp,
                          packet = RealTailAgreementSealUp.mk R S W D A H C P N) →
                          UnaryHistory agreementRead ∧ UnaryHistory finalRead ∧
                            Cont W D agreementRead ∧ Cont agreementRead A finalRead ∧
                              hsame agreementRead (append W D) ∧
                                hsame finalRead (append (append W D) A) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro rootUnary limiterUnary selectorUnary windowUnary dyadicUnary agreementUnary
  intro rootLimiterRoute tailSelectorRoute windowDyadicRoute agreementFinalRoute packet
  obtain ⟨_packet, packetEq⟩ := packet
  cases packetEq
  have _tailBudgetUnary : UnaryHistory tailBudget :=
    unary_cont_closed rootUnary limiterUnary rootLimiterRoute
  have _windowFromSelectorUnary : UnaryHistory W :=
    unary_cont_closed _tailBudgetUnary selectorUnary tailSelectorRoute
  have agreementReadUnary : UnaryHistory agreementRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicRoute
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed agreementReadUnary agreementUnary agreementFinalRoute
  have agreementExact : hsame agreementRead (append W D) := by
    cases windowDyadicRoute
    rfl
  have finalExact : hsame finalRead (append (append W D) A) := by
    cases windowDyadicRoute
    cases agreementFinalRoute
    rfl
  exact
    ⟨agreementReadUnary, finalReadUnary, windowDyadicRoute, agreementFinalRoute,
      agreementExact, finalExact⟩

end BEDC.Derived.RealTailAgreementSealUp
