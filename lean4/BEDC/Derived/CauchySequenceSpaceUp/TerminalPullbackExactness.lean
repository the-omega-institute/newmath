import BEDC.Derived.CauchySequenceSpaceUp

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceSpaceCarrier_terminal_pullback_exactness [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route name streamFace dyadicFace
      realFace exactBoundary terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      UnaryHistory exactBoundary ->
        Cont family schedule streamFace ->
          Cont streamFace tolerance dyadicFace ->
            Cont dyadicFace route realFace ->
              Cont realFace exactBoundary terminal ->
                PkgSig bundle terminal pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        UnaryHistory row ∧ hsame row terminal ∧ PkgSig bundle terminal pkg)
                      (fun row : BHist =>
                        Cont realFace exactBoundary row ∧ PkgSig bundle terminal pkg)
                      (fun row : BHist =>
                        UnaryHistory realFace ∧ UnaryHistory exactBoundary ∧ hsame row terminal)
                      hsame ∧
                    UnaryHistory streamFace ∧ UnaryHistory dyadicFace ∧
                      UnaryHistory realFace ∧ UnaryHistory terminal ∧ hsame window streamFace ∧
                        hsame completion dyadicFace ∧ Cont family schedule streamFace ∧
                          Cont streamFace tolerance dyadicFace ∧ Cont dyadicFace route realFace ∧
                            Cont realFace exactBoundary terminal ∧
                              PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert UnaryHistory
  intro carrier exactBoundaryUnary familyScheduleStream streamToleranceDyadic dyadicRouteReal
    realExactTerminal terminalPkg
  obtain ⟨familyUnary, scheduleUnary, _windowUnary, toleranceUnary, _completionUnary,
    _transportUnary, routeUnary, _nameUnary, familyScheduleWindow, windowToleranceCompletion,
    _completionTransportRoute, _routePkg, _namePkg⟩ := carrier
  have streamFaceUnary : UnaryHistory streamFace :=
    unary_cont_closed familyUnary scheduleUnary familyScheduleStream
  have dyadicFaceUnary : UnaryHistory dyadicFace :=
    unary_cont_closed streamFaceUnary toleranceUnary streamToleranceDyadic
  have realFaceUnary : UnaryHistory realFace :=
    unary_cont_closed dyadicFaceUnary routeUnary dyadicRouteReal
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed realFaceUnary exactBoundaryUnary realExactTerminal
  have sameWindow : hsame window streamFace :=
    cont_respects_hsame (hsame_refl family) (hsame_refl schedule) familyScheduleWindow
      familyScheduleStream
  have sameCompletion : hsame completion dyadicFace :=
    cont_respects_hsame sameWindow (hsame_refl tolerance) windowToleranceCompletion
      streamToleranceDyadic
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          UnaryHistory row ∧ hsame row terminal ∧ PkgSig bundle terminal pkg)
        (fun row : BHist =>
          Cont realFace exactBoundary row ∧ PkgSig bundle terminal pkg)
        (fun row : BHist =>
          UnaryHistory realFace ∧ UnaryHistory exactBoundary ∧ hsame row terminal)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro terminal ⟨terminalUnary, hsame_refl terminal, terminalPkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact
          ⟨unary_transport sourceRow.left sameRows,
            hsame_trans (hsame_symm sameRows) sourceRow.right.left,
            sourceRow.right.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨cont_result_hsame_transport realExactTerminal (hsame_symm sourceRow.right.left),
          sourceRow.right.right⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨realFaceUnary, exactBoundaryUnary, sourceRow.right.left⟩
  }
  exact
    ⟨cert, streamFaceUnary, dyadicFaceUnary, realFaceUnary, terminalUnary, sameWindow,
      sameCompletion, familyScheduleStream, streamToleranceDyadic, dyadicRouteReal,
      realExactTerminal, terminalPkg⟩

end BEDC.Derived.CauchySequenceSpaceUp
