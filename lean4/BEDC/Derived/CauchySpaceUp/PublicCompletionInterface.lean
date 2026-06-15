import BEDC.Derived.CauchySpaceUp

namespace BEDC.Derived.CauchySpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchySpaceCarrier_precompletion_terminal_interface
    {F0 F1 U0 R0 T0 H0 C0 P0 N0 regular completion named publicRead terminal : BHist} :
    CauchySpaceLocalFilterCarrier F0 F1 U0 R0 T0 H0 C0 P0 N0 ->
      Cont R0 F1 regular ->
        Cont regular T0 completion ->
          Cont completion P0 named ->
            Cont named N0 publicRead ->
              Cont publicRead N0 terminal ->
                UnaryHistory R0 ∧ UnaryHistory F1 ∧ UnaryHistory T0 ∧
                  UnaryHistory regular ∧ UnaryHistory completion ∧ UnaryHistory named ∧
                    UnaryHistory publicRead ∧ UnaryHistory terminal ∧
                      Cont R0 F1 regular ∧ Cont regular T0 completion ∧
                        Cont completion P0 named ∧ Cont named N0 publicRead ∧
                          Cont publicRead N0 terminal ∧ hsame H0 (append F0 U0) := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro localCarrier regularRoute completionRoute namedRoute publicReadRoute terminalRoute
  obtain ⟨carrier, _localPrecompletionRoute⟩ := localCarrier
  have nonescape :=
    CauchySpaceCarrier_precompletion_nonescape_obligation
      (F := F0) (U := U0) (R := R0) (Q := F1) (T := T0) (H := H0)
      (C := C0) (P := P0) (N := N0) (handoff := regular)
      (consumer := completion)
      carrier regularRoute completionRoute
  obtain ⟨rUnary, f1Unary, tUnary, regularUnary, completionUnary, regularRouteOut,
    completionRouteOut, transportRow⟩ := nonescape
  obtain ⟨_fUnary, _uUnary, _rUnary, _f1Unary, _tUnary, _hUnary, _cUnary, pUnary,
    nUnary, _transportRow, _carrierFilterRoute, _nameRoute⟩ := carrier
  have namedUnary : UnaryHistory named :=
    unary_cont_closed completionUnary pUnary namedRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed namedUnary nUnary publicReadRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed publicReadUnary nUnary terminalRoute
  exact
    ⟨rUnary, f1Unary, tUnary, regularUnary, completionUnary, namedUnary, publicReadUnary,
      terminalUnary, regularRouteOut, completionRouteOut, namedRoute, publicReadRoute,
      terminalRoute, transportRow⟩

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
