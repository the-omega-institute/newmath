import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_phase_real_classifier_readiness
    {Z S M R Q H C P N phaseRead classifierRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont R Q phaseRead ->
        Cont phaseRead H classifierRead ->
          UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory phaseRead ∧
            UnaryHistory classifierRead ∧ hsame H (append Z S) ∧ Cont R Q phaseRead ∧
              Cont phaseRead H classifierRead ∧ Cont M R Q ∧ Cont Q H C ∧
                Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet phaseRoute classifierRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed unaryR unaryQ phaseRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed phaseUnary unaryH classifierRoute
  exact
    ⟨unaryR, unaryQ, unaryH, phaseUnary, classifierUnary, sameH, phaseRoute,
      classifierRoute, routeQ, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_phase_real_classifier_determinacy
    {Z S M R Q H C P N Z' S' M' R' Q' H' C' P' N' phaseRead phaseRead' : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      CriticalLineWitnessCarrier Z' S' M' R' Q' H' C' P' N' ->
        hsame Z Z' ->
          hsame S S' ->
            hsame M M' ->
              hsame R R' ->
                hsame Q Q' ->
                  hsame H H' ->
                    hsame C C' ->
                      hsame P P' ->
                        hsame N N' ->
                          Cont Z S phaseRead ->
                            Cont Z' S' phaseRead' -> hsame phaseRead phaseRead' := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro _packet _packet' sameZ sameS _sameM _sameR _sameQ _sameH _sameC _sameP _sameN
    phaseRoute phaseRoute'
  exact cont_respects_hsame sameZ sameS phaseRoute phaseRoute'

end BEDC.Derived.CriticalLineWitnessUp
