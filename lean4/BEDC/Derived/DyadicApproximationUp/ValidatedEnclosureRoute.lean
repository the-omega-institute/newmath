import BEDC.Derived.DyadicApproximationUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_validated_enclosure_route_commutation
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint
      terminalWindow terminalLedger terminalProvenance meshCell validatedEnclosure sealRow
      dyadicRead meshRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision terminalPrecision ->
        hsame endpoint terminalEndpoint ->
          hsame ledger terminalLedger ->
            hsame provenance terminalProvenance ->
              Cont terminalPrecision terminalEndpoint terminalWindow ->
                Cont terminalWindow terminalLedger terminalProvenance ->
                  Cont terminalWindow terminalProvenance meshCell ->
                    Cont meshCell terminalProvenance validatedEnclosure ->
                      Cont terminalLedger terminalProvenance sealRow ->
                        Cont terminalWindow terminalProvenance dyadicRead ->
                          Cont meshCell terminalProvenance meshRead ->
                            PkgSig bundle meshCell pkg ->
                              PkgSig bundle validatedEnclosure pkg ->
                                PkgSig bundle sealRow pkg ->
                                  SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row validatedEnclosure ∧ UnaryHistory row ∧
                                        PkgSig bundle row pkg)
                                    (fun row : BHist =>
                                      Cont meshCell terminalProvenance row ∧
                                        hsame window terminalWindow)
                                    (fun row : BHist =>
                                      PkgSig bundle row pkg ∧ UnaryHistory sealRow ∧
                                        UnaryHistory dyadicRead ∧ UnaryHistory meshRead)
                                    (fun row row' : BHist => hsame row row') := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
    terminalPrecisionEndpointWindow terminalWindowLedgerProvenance terminalWindowProvenanceMesh
    meshProvenanceEnclosure terminalLedgerProvenanceSeal terminalWindowProvenanceDyadicRead
    meshProvenanceMeshRead _meshPkg enclosurePkg sealPkg
  have transported :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        hsame window terminalWindow :=
    DyadicApproximationCarrier_classifier_transport carrier samePrecision sameEndpoint
      sameLedger sameProvenance terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  obtain ⟨terminalCarrier, sameWindow⟩ := transported
  obtain ⟨_terminalPrecisionUnary, _terminalEndpointUnary, terminalWindowUnary,
    terminalLedgerUnary, terminalProvenanceUnary, _terminalWindowRow,
    _terminalProvenanceRow, _terminalPkg⟩ := terminalCarrier
  have meshUnary : UnaryHistory meshCell :=
    unary_cont_closed terminalWindowUnary terminalProvenanceUnary terminalWindowProvenanceMesh
  have enclosureUnary : UnaryHistory validatedEnclosure :=
    unary_cont_closed meshUnary terminalProvenanceUnary meshProvenanceEnclosure
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed terminalLedgerUnary terminalProvenanceUnary terminalLedgerProvenanceSeal
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed terminalWindowUnary terminalProvenanceUnary terminalWindowProvenanceDyadicRead
  have meshReadUnary : UnaryHistory meshRead :=
    unary_cont_closed meshUnary terminalProvenanceUnary meshProvenanceMeshRead
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro validatedEnclosure
          ⟨hsame_refl validatedEnclosure, enclosureUnary, enclosurePkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' classified
        exact hsame_symm classified
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact hsame_trans leftClassified rightClassified
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified
        exact sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      exact
        ⟨cont_result_hsame_transport meshProvenanceEnclosure (hsame_symm sourceRow.left),
          sameWindow⟩
    ledger_sound := by
      intro row sourceRow
      exact ⟨sourceRow.right.right, sealUnary, dyadicReadUnary, meshReadUnary⟩
  }

end BEDC.Derived.DyadicApproximationUp
