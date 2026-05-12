import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_diagonal_mesh_selector_boundary
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint
      terminalWindow terminalLedger terminalProvenance meshCell diagonalWindow meshRead
      diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision terminalPrecision ->
        hsame endpoint terminalEndpoint ->
          hsame ledger terminalLedger ->
            hsame provenance terminalProvenance ->
              Cont terminalPrecision terminalEndpoint terminalWindow ->
                Cont terminalWindow terminalLedger terminalProvenance ->
                  Cont terminalWindow terminalProvenance meshCell ->
                    Cont terminalWindow terminalProvenance diagonalWindow ->
                      hsame meshCell diagonalWindow ->
                        Cont meshCell terminalProvenance meshRead ->
                          Cont diagonalWindow terminalProvenance diagonalRead ->
                            PkgSig bundle meshRead pkg ->
                              PkgSig bundle diagonalRead pkg ->
                                UnaryHistory meshCell ∧ UnaryHistory diagonalWindow ∧
                                  UnaryHistory meshRead ∧ UnaryHistory diagonalRead ∧
                                    hsame meshRead diagonalRead ∧ hsame window terminalWindow ∧
                                      PkgSig bundle meshRead pkg ∧
                                        PkgSig bundle diagonalRead pkg := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
    terminalPrecisionEndpointWindow terminalWindowLedgerProvenance terminalWindowMesh
    terminalWindowDiagonal sameMeshDiagonal meshReadRoute diagonalReadRoute meshReadPkg
    diagonalReadPkg
  have transported :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        hsame window terminalWindow :=
    DyadicApproximationCarrier_classifier_transport carrier samePrecision sameEndpoint
      sameLedger sameProvenance terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  obtain ⟨terminalCarrier, sameWindow⟩ := transported
  obtain ⟨_terminalPrecisionUnary, _terminalEndpointUnary, terminalWindowUnary,
    _terminalLedgerUnary, terminalProvenanceUnary, _terminalWindowRoute,
    _terminalProvenanceRoute, _terminalPkg⟩ := terminalCarrier
  have meshUnary : UnaryHistory meshCell :=
    unary_cont_closed terminalWindowUnary terminalProvenanceUnary terminalWindowMesh
  have diagonalUnary : UnaryHistory diagonalWindow :=
    unary_cont_closed terminalWindowUnary terminalProvenanceUnary terminalWindowDiagonal
  have meshReadUnary : UnaryHistory meshRead :=
    unary_cont_closed meshUnary terminalProvenanceUnary meshReadRoute
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed diagonalUnary terminalProvenanceUnary diagonalReadRoute
  have sameRead : hsame meshRead diagonalRead :=
    cont_respects_hsame sameMeshDiagonal (hsame_refl terminalProvenance) meshReadRoute
      diagonalReadRoute
  exact
    ⟨meshUnary, diagonalUnary, meshReadUnary, diagonalReadUnary, sameRead, sameWindow,
      meshReadPkg, diagonalReadPkg⟩

end BEDC.Derived.DyadicApproximationUp
