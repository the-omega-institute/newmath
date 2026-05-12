import BEDC.Derived.DyadicApproximationUp.ValidatedEnclosureRoute

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_refinement_seal_commutation [AskSetup] [PackageSetup]
    {precisionA endpointA windowA ledgerA provenanceA precisionB endpointB windowB ledgerB
      provenanceB commonPrecision commonEndpoint commonWindow commonLedger commonProvenance
      meshCell validatedEnclosure sealRow dyadicRead meshRead : BHist}
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
                                Cont commonLedger commonProvenance sealRow ->
                                  Cont commonWindow commonProvenance dyadicRead ->
                                    Cont meshCell commonProvenance meshRead ->
                                      PkgSig bundle meshCell pkg ->
                                        PkgSig bundle validatedEnclosure pkg ->
                                          PkgSig bundle sealRow pkg ->
                                            DyadicApproximationCarrier commonPrecision
                                                commonEndpoint commonWindow commonLedger
                                                commonProvenance bundle pkg ∧
                                              hsame windowA commonWindow ∧
                                                hsame windowB commonWindow ∧
                                                  SemanticNameCert
                                                    (fun row : BHist =>
                                                      hsame row validatedEnclosure ∧
                                                        UnaryHistory row ∧
                                                          PkgSig bundle row pkg)
                                                    (fun row : BHist =>
                                                      Cont meshCell commonProvenance row ∧
                                                        hsame windowA commonWindow)
                                                    (fun row : BHist =>
                                                      PkgSig bundle row pkg ∧
                                                        UnaryHistory sealRow ∧
                                                          UnaryHistory dyadicRead ∧
                                                            UnaryHistory meshRead)
                                                    (fun row row' : BHist =>
                                                      hsame row row') := by
  intro carrierA carrierB samePrecisionA samePrecisionB sameEndpointA sameEndpointB
  intro sameLedgerA sameLedgerB sameProvenanceA sameProvenanceB
  intro commonPrecisionEndpointWindow commonWindowLedgerProvenance
  intro commonWindowProvenanceMesh meshProvenanceValidated commonLedgerProvenanceSeal
  intro commonWindowProvenanceDyadicRead meshProvenanceMeshRead meshPkg validatedPkg sealPkg
  have refined :
      DyadicApproximationCarrier commonPrecision commonEndpoint commonWindow commonLedger
          commonProvenance bundle pkg ∧
        hsame windowA commonWindow ∧ hsame windowB commonWindow :=
    DyadicApproximationCarrier_common_precision_refinement carrierA carrierB samePrecisionA
      samePrecisionB sameEndpointA sameEndpointB sameLedgerA sameLedgerB sameProvenanceA
      sameProvenanceB commonPrecisionEndpointWindow commonWindowLedgerProvenance
  have routeCert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row validatedEnclosure ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist =>
          Cont meshCell commonProvenance row ∧ hsame windowA commonWindow)
        (fun row : BHist =>
          PkgSig bundle row pkg ∧ UnaryHistory sealRow ∧ UnaryHistory dyadicRead ∧
            UnaryHistory meshRead)
        (fun row row' : BHist => hsame row row') :=
    DyadicApproximationCarrier_validated_enclosure_route_commutation carrierA
      samePrecisionA sameEndpointA sameLedgerA sameProvenanceA
      commonPrecisionEndpointWindow commonWindowLedgerProvenance commonWindowProvenanceMesh
      meshProvenanceValidated commonLedgerProvenanceSeal commonWindowProvenanceDyadicRead
      meshProvenanceMeshRead meshPkg validatedPkg sealPkg
  exact ⟨refined.left, refined.right.left, refined.right.right, routeCert⟩

end BEDC.Derived.DyadicApproximationUp
