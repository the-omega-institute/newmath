import BEDC.Derived.CauchySpaceUp

namespace BEDC.Derived.CauchySpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchySpaceCarrier_public_completion_interface
    {F0 F1 U0 R0 T0 H0 C0 P0 N0 completion named publicRead terminal : BHist} :
    CauchySpaceLocalFilterCarrier F0 F1 U0 R0 T0 H0 C0 P0 N0 ->
      Cont F0 U0 R0 ->
        Cont R0 T0 completion ->
          Cont completion P0 named ->
            Cont named N0 publicRead ->
              Cont publicRead N0 terminal ->
                UnaryHistory F0 ∧ UnaryHistory F1 ∧ UnaryHistory U0 ∧
                  UnaryHistory R0 ∧ UnaryHistory T0 ∧ UnaryHistory H0 ∧
                    UnaryHistory completion ∧ UnaryHistory named ∧
                      UnaryHistory publicRead ∧ UnaryHistory terminal ∧
                        hsame H0 (append F0 U0) ∧ Cont F0 U0 R0 ∧
                          Cont R0 T0 H0 ∧ Cont R0 T0 completion ∧
                            Cont completion P0 named ∧ Cont named N0 publicRead ∧
                              Cont publicRead N0 terminal := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro localCarrier filterRoute completionRoute namedRoute publicReadRoute terminalRoute
  have boundary :=
    CauchySpaceCarrier_public_consumer_boundary
      (F0 := F0) (F1 := F1) (U0 := U0) (R0 := R0) (T0 := T0) (H0 := H0)
      (C0 := C0) (P0 := P0) (N0 := N0) (completion := completion) (named := named)
      (publicRead := publicRead)
      localCarrier filterRoute completionRoute namedRoute publicReadRoute
  obtain ⟨fUnary, f1Unary, uUnary, rUnary, tUnary, hUnary, completionUnary, namedUnary,
    publicReadUnary, transportRow, filterRouteOut, localPrecompletionRoute,
    completionRouteOut, namedRouteOut, publicReadRouteOut⟩ := boundary
  obtain ⟨carrier, _localPrecompletionRoute⟩ := localCarrier
  obtain ⟨_fUnary, _uUnary, _rUnary, _f1Unary, _tUnary, _hUnary, _cUnary, _pUnary,
    nUnary, _transportRow, _carrierFilterRoute, _nameRoute⟩ := carrier
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed publicReadUnary nUnary terminalRoute
  exact
    ⟨fUnary, f1Unary, uUnary, rUnary, tUnary, hUnary, completionUnary, namedUnary,
      publicReadUnary, terminalUnary, transportRow, filterRouteOut, localPrecompletionRoute,
      completionRouteOut, namedRouteOut, publicReadRouteOut, terminalRoute⟩

end BEDC.Derived.CauchySpaceUp
