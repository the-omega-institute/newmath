import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_finite_budget_readback_determinacy
    {Z S M R Q H C P N Z' S' M' R' Q' H' C' P' N' read read' : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      CriticalLineWitnessCarrier Z' S' M' R' Q' H' C' P' N' →
        hsame Z Z' →
          hsame S S' →
            hsame M M' →
              hsame R R' →
                hsame Q Q' →
                  hsame H H' →
                    hsame C C' →
                      hsame P P' →
                        hsame N N' →
                          Cont (append Z S) Q read →
                            Cont (append Z' S') Q' read' →
                              hsame read read' ∧ UnaryHistory read ∧ UnaryHistory read' ∧
                                hsame H (append Z S) ∧ hsame H' (append Z' S') := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet packet' sameZ sameS _sameM _sameR sameQ _sameH _sameC _sameP _sameN
    readRoute readRoute'
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameSource, routeQ, routeC, routeN⟩ :=
    packet
  obtain
    ⟨unaryZ', unaryS', unaryM', unaryR', _unaryP', sameSource', routeQ', routeC',
      routeN'⟩ := packet'
  have sameAppend : hsame (append Z S) (append Z' S') :=
    cont_respects_hsame sameZ sameS (cont_intro rfl) (cont_intro rfl)
  have sameRead : hsame read read' :=
    cont_respects_hsame sameAppend sameQ readRoute readRoute'
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryQ' : UnaryHistory Q' :=
    unary_cont_closed unaryM' unaryR' routeQ'
  have unaryRead : UnaryHistory read :=
    unary_cont_closed (unary_cont_closed unaryZ unaryS (cont_intro rfl)) unaryQ readRoute
  have unaryRead' : UnaryHistory read' :=
    unary_cont_closed (unary_cont_closed unaryZ' unaryS' (cont_intro rfl)) unaryQ' readRoute'
  exact ⟨sameRead, unaryRead, unaryRead', sameSource, sameSource'⟩

end BEDC.Derived.CriticalLineWitnessUp
