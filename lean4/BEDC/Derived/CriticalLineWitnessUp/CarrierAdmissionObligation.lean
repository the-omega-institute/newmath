import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_admission_obligation
    {Z S M R Q H C P N admissionRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S admissionRead ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
          UnaryHistory Q ∧ UnaryHistory admissionRead ∧ hsame H (append Z S) ∧
            Cont Z S admissionRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet admissionRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q := unary_cont_closed unaryM unaryR routeQ
  have admissionUnary : UnaryHistory admissionRead :=
    unary_cont_closed unaryZ unaryS admissionRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, admissionUnary, sameH, admissionRoute, routeQ,
      routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
