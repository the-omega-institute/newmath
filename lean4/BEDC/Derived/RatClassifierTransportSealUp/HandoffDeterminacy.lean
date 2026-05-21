import BEDC.Derived.RatClassifierTransportSealUp.WindowExhaustion

namespace BEDC.Derived.RatClassifierTransportSealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem rat_classifier_transport_seal_handoff_determinacy_readback
    {Q S W D A H C N realRead realRead' : BHist} :
    FieldFaithful.fields (RatClassifierTransportSealUp.mk Q S W D A H C N) =
        [Q, S, W, D, A, H, C, N] →
      UnaryHistory Q →
        UnaryHistory S →
          UnaryHistory D →
            UnaryHistory H →
              Cont Q S W →
                Cont W D A →
                  Cont A H realRead →
                    Cont A H realRead' →
                      UnaryHistory realRead ∧ UnaryHistory realRead' ∧
                        hsame realRead realRead' ∧ Cont A H realRead ∧
                          Cont A H realRead' := by
  intro fields unaryQ unaryS unaryD unaryH routeQS routeWD routeAH routeAH'
  have windowFacts :
      UnaryHistory W ∧ UnaryHistory A ∧ UnaryHistory realRead ∧ Cont Q S W ∧
        Cont W D A ∧ Cont A H realRead :=
    RatClassifierTransportSealCarrier_window_exhaustion fields unaryQ unaryS unaryD unaryH
      routeQS routeWD routeAH
  obtain ⟨_unaryW, unaryA, unaryRead, _routeQS, _routeWD, routeAHStored⟩ := windowFacts
  have unaryRead' : UnaryHistory realRead' :=
    unary_cont_closed unaryA unaryH routeAH'
  have sameRead : hsame realRead realRead' :=
    cont_respects_hsame (hsame_refl A) (hsame_refl H) routeAHStored routeAH'
  exact ⟨unaryRead, unaryRead', sameRead, routeAHStored, routeAH'⟩

end BEDC.Derived.RatClassifierTransportSealUp
