import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_strip_classifier_stability
    {Z S M R Q H C P N Z' S' M' R' Q' H' C' P' N' classifierRead
      transportedRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      CriticalLineWitnessCarrier Z' S' M' R' Q' H' C' P' N' ->
        hsame H H' ->
          hsame Q Q' ->
            Cont (append Z S) Q classifierRead ->
              Cont (append Z' S') Q' transportedRead ->
                hsame classifierRead transportedRead ∧
                  UnaryHistory classifierRead ∧ UnaryHistory transportedRead ∧
                    hsame H (append Z S) ∧ hsame H' (append Z' S') := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro sourcePacket targetPacket sameHSource sameQ classifierRoute transportedRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    sourcePacket
  obtain
    ⟨unaryZ', unaryS', unaryM', unaryR', _unaryP', sameH', routeQ', _routeC',
      _routeN'⟩ := targetPacket
  have sameSource : hsame (append Z S) (append Z' S') :=
    hsame_trans (hsame_symm sameH) (hsame_trans sameHSource sameH')
  have sameClassifier : hsame classifierRead transportedRead :=
    cont_respects_hsame sameSource sameQ classifierRoute transportedRoute
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have targetSourceUnary : UnaryHistory (append Z' S') :=
    unary_cont_closed unaryZ' unaryS' (cont_intro rfl)
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryQ' : UnaryHistory Q' :=
    unary_cont_closed unaryM' unaryR' routeQ'
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed sourceUnary unaryQ classifierRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed targetSourceUnary unaryQ' transportedRoute
  exact ⟨sameClassifier, classifierUnary, transportedUnary, sameH, sameH'⟩

end BEDC.Derived.CriticalLineWitnessUp
