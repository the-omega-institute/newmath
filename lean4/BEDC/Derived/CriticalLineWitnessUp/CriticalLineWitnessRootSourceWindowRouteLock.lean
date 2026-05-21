import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_source_window_route_lock
    {Z S M R Q H C P N sourceRead modulusRead consumerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q sourceRead ->
        Cont M R modulusRead ->
          Cont sourceRead modulusRead consumerRead ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory sourceRead ∧
                UnaryHistory modulusRead ∧ UnaryHistory consumerRead ∧
                  hsame H (append Z S) ∧ Cont M R Q ∧
                    Cont (append Z S) Q sourceRead ∧ Cont M R modulusRead ∧
                      Cont sourceRead modulusRead consumerRead ∧ Cont Q H C ∧
                        Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet sourceRoute modulusRoute consumerRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryRoot : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryRoot (hsame_symm sameH)
  have unarySourceRead : UnaryHistory sourceRead :=
    unary_cont_closed unaryRoot unaryQ sourceRoute
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have unaryConsumerRead : UnaryHistory consumerRead :=
    unary_cont_closed unarySourceRead unaryModulusRead consumerRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unarySourceRead,
      unaryModulusRead, unaryConsumerRead, sameH, routeQ, sourceRoute, modulusRoute,
      consumerRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
