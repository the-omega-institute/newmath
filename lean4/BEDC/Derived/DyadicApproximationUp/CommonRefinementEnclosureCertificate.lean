import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_common_refinement_enclosure_certificate
    [AskSetup] [PackageSetup]
    {precisionA endpointA windowA ledgerA provenanceA precisionB endpointB windowB ledgerB
      provenanceB commonPrecision commonEndpoint commonWindow commonLedger commonProvenance
      meshCell validatedEnclosure realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precisionA endpointA windowA ledgerA provenanceA bundle pkg ->
      DyadicApproximationCarrier precisionB endpointB windowB ledgerB provenanceB bundle pkg ->
        hsame precisionA commonPrecision ->
          hsame precisionB commonPrecision ->
            hsame endpointA commonEndpoint ->
              hsame endpointB commonEndpoint ->
                hsame ledgerA commonLedger ->
                  hsame ledgerB commonLedger ->
                    hsame provenanceA commonProvenance ->
                      hsame provenanceB commonProvenance ->
                        Cont commonPrecision commonEndpoint commonWindow ->
                          Cont commonWindow commonLedger commonProvenance ->
                            Cont commonWindow commonProvenance meshCell ->
                              Cont meshCell commonProvenance validatedEnclosure ->
                                Cont commonLedger commonProvenance realSeal ->
                                  PkgSig bundle meshCell pkg ->
                                    PkgSig bundle validatedEnclosure pkg ->
                                      PkgSig bundle realSeal pkg ->
                                        SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row commonWindow ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            DyadicApproximationCarrier commonPrecision
                                                commonEndpoint row commonLedger
                                                commonProvenance bundle pkg ∧
                                              Cont row commonProvenance meshCell ∧
                                                Cont meshCell commonProvenance
                                                  validatedEnclosure ∧
                                                  Cont commonLedger commonProvenance realSeal)
                                          (fun _row : BHist =>
                                            PkgSig bundle meshCell pkg ∧
                                              PkgSig bundle validatedEnclosure pkg ∧
                                                PkgSig bundle realSeal pkg)
                                          hsame := by
  intro carrierA carrierB samePrecisionA samePrecisionB sameEndpointA sameEndpointB
  intro sameLedgerA sameLedgerB sameProvenanceA sameProvenanceB
  intro commonPrecisionEndpointWindow commonWindowLedgerProvenance
  intro commonWindowProvenanceMesh meshProvenanceEnclosure commonLedgerProvenanceSeal
  intro meshPkg enclosurePkg sealPkg
  have refined :
      DyadicApproximationCarrier commonPrecision commonEndpoint commonWindow commonLedger
          commonProvenance bundle pkg ∧
        hsame windowA commonWindow ∧ hsame windowB commonWindow :=
    DyadicApproximationCarrier_common_precision_refinement carrierA carrierB samePrecisionA
      samePrecisionB sameEndpointA sameEndpointB sameLedgerA sameLedgerB sameProvenanceA
      sameProvenanceB commonPrecisionEndpointWindow commonWindowLedgerProvenance
  obtain ⟨commonCarrier, _sameWindowA, _sameWindowB⟩ := refined
  obtain ⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
    precisionEndpointWindow, windowLedgerProvenance, provenancePkg⟩ := commonCarrier
  have meshUnary : UnaryHistory meshCell :=
    unary_cont_closed windowUnary provenanceUnary commonWindowProvenanceMesh
  have enclosureUnary : UnaryHistory validatedEnclosure :=
    unary_cont_closed meshUnary provenanceUnary meshProvenanceEnclosure
  have sealUnary : UnaryHistory realSeal :=
    unary_cont_closed ledgerUnary provenanceUnary commonLedgerProvenanceSeal
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro commonWindow ⟨hsame_refl commonWindow, windowUnary⟩
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
      cases sourceRow.left
      exact
        ⟨⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
            precisionEndpointWindow, windowLedgerProvenance, provenancePkg⟩,
          commonWindowProvenanceMesh, meshProvenanceEnclosure, commonLedgerProvenanceSeal⟩
    ledger_sound := by
      intro _row _sourceRow
      exact ⟨meshPkg, enclosurePkg, sealPkg⟩
  }

end BEDC.Derived.DyadicApproximationUp
