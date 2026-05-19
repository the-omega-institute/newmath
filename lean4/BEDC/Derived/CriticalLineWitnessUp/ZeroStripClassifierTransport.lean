import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_strip_classifier_transport
    {Z S M R Q H C P N zeroStripRead modulusRead classifierRead transportedClassifier : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        Cont M R modulusRead ->
          Cont zeroStripRead modulusRead classifierRead ->
            Cont classifierRead H transportedClassifier ->
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧
                UnaryHistory zeroStripRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory classifierRead ∧ UnaryHistory transportedClassifier ∧
                    hsame H (append Z S) ∧ Cont Q H C ∧
                      Cont classifierRead H transportedClassifier ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist append hsame Cont UnaryHistory
  intro packet zeroStripRoute modulusRoute classifierRoute transportedRoute
  have comparison :
      UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory Q ∧ UnaryHistory zeroStripRead ∧ UnaryHistory modulusRead ∧
          UnaryHistory classifierRead ∧ hsame H (append Z S) ∧
            Cont Z S zeroStripRead ∧ Cont M R Q ∧ Cont M R modulusRead ∧
              Cont zeroStripRead modulusRead classifierRead ∧ Cont Q H C ∧ Cont C P N :=
    CriticalLineWitnessCarrier_root_strip_comparison_classifier packet zeroStripRoute
      modulusRoute classifierRoute
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, unaryQ, unaryZeroStripRead,
    unaryModulusRead, unaryClassifierRead, sameH, _zeroStripRoute, _routeQ,
    _modulusRoute, _classifierRoute, routeC, routeN⟩ := comparison
  have transportedUnary : UnaryHistory transportedClassifier :=
    unary_cont_closed unaryClassifierRead
      (unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH))
      transportedRoute
  exact
    ⟨unaryZ, unaryS, unaryQ, unaryZeroStripRead, unaryModulusRead, unaryClassifierRead,
      transportedUnary, sameH, routeC, transportedRoute, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
