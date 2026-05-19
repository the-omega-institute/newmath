import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_strip_source_classifier_lock
    {Z S M R Q H C P N sourceRead classifierRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S sourceRead →
        Cont sourceRead H classifierRead →
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory sourceRead ∧
            UnaryHistory classifierRead ∧ hsame H (append Z S) ∧
              Cont Z S sourceRead ∧ Cont sourceRead H classifierRead ∧ Cont M R Q ∧
                Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist append hsame Cont UnaryHistory
  intro packet sourceRoute classifierRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have sourceAppendUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceAppendUnary (hsame_symm sameH)
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed sourceUnary unaryH classifierRoute
  exact
    ⟨unaryZ, unaryS, sourceUnary, classifierUnary, sameH, sourceRoute,
      classifierRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
