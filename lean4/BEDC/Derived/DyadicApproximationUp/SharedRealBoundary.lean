import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_shared_real_boundary_determinacy [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance precision' endpoint' window' ledger'
      provenance' sharedPrecision sharedEndpoint sharedWindow sharedLedger sharedProvenance
      meshCell validatedRead realSeal consumer consumer' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      DyadicApproximationCarrier precision' endpoint' window' ledger' provenance' bundle pkg ->
        hsame precision sharedPrecision ->
          hsame precision' sharedPrecision ->
            hsame endpoint sharedEndpoint ->
              hsame endpoint' sharedEndpoint ->
                hsame ledger sharedLedger ->
                  hsame ledger' sharedLedger ->
                    hsame provenance sharedProvenance ->
                      hsame provenance' sharedProvenance ->
                        Cont sharedPrecision sharedEndpoint sharedWindow ->
                          Cont sharedWindow sharedLedger sharedProvenance ->
                            Cont sharedWindow sharedProvenance meshCell ->
                              Cont meshCell sharedProvenance validatedRead ->
                                Cont sharedLedger sharedProvenance realSeal ->
                                  Cont validatedRead realSeal consumer ->
                                    Cont validatedRead realSeal consumer' ->
                                      PkgSig bundle meshCell pkg ->
                                        PkgSig bundle validatedRead pkg ->
                                          PkgSig bundle realSeal pkg ->
                                            PkgSig bundle consumer pkg ->
                                              PkgSig bundle consumer' pkg ->
                                                DyadicApproximationCarrier sharedPrecision
                                                    sharedEndpoint sharedWindow sharedLedger
                                                    sharedProvenance bundle pkg ∧
                                                  UnaryHistory meshCell ∧
                                                    UnaryHistory validatedRead ∧
                                                      UnaryHistory realSeal ∧
                                                        UnaryHistory consumer ∧
                                                          UnaryHistory consumer' ∧
                                                            hsame window sharedWindow ∧
                                                              hsame window' sharedWindow ∧
                                                                hsame consumer consumer' ∧
                                                                  PkgSig bundle consumer
                                                                    pkg ∧
                                                                    PkgSig bundle consumer'
                                                                      pkg := by
  intro carrier carrier' samePrecision samePrecision' sameEndpoint sameEndpoint'
  intro sameLedger sameLedger' sameProvenance sameProvenance'
  intro sharedPrecisionEndpointWindow sharedWindowLedgerProvenance
  intro sharedWindowProvenanceMesh meshProvenanceValidated sharedLedgerProvenanceSeal
  intro validatedSealConsumer validatedSealConsumer' _meshPkg _validatedPkg _sealPkg
  intro consumerPkg consumerPkg'
  have refined :
      DyadicApproximationCarrier sharedPrecision sharedEndpoint sharedWindow sharedLedger
          sharedProvenance bundle pkg ∧
        hsame window sharedWindow ∧ hsame window' sharedWindow :=
    DyadicApproximationCarrier_common_precision_refinement carrier carrier'
      samePrecision samePrecision' sameEndpoint sameEndpoint' sameLedger sameLedger'
      sameProvenance sameProvenance' sharedPrecisionEndpointWindow
      sharedWindowLedgerProvenance
  rcases refined with ⟨sharedCarrier, sameWindow, sameWindow'⟩
  rcases sharedCarrier with
    ⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
      precisionEndpointWindow, windowLedgerProvenance, provenancePkg⟩
  have meshUnary : UnaryHistory meshCell :=
    unary_cont_closed windowUnary provenanceUnary sharedWindowProvenanceMesh
  have validatedUnary : UnaryHistory validatedRead :=
    unary_cont_closed meshUnary provenanceUnary meshProvenanceValidated
  have sealUnary : UnaryHistory realSeal :=
    unary_cont_closed ledgerUnary provenanceUnary sharedLedgerProvenanceSeal
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed validatedUnary sealUnary validatedSealConsumer
  have consumerUnary' : UnaryHistory consumer' :=
    unary_cont_closed validatedUnary sealUnary validatedSealConsumer'
  have sameConsumer : hsame consumer consumer' :=
    cont_deterministic validatedSealConsumer validatedSealConsumer'
  exact
    ⟨⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
        precisionEndpointWindow, windowLedgerProvenance, provenancePkg⟩,
      meshUnary, validatedUnary, sealUnary, consumerUnary, consumerUnary', sameWindow,
      sameWindow', sameConsumer, consumerPkg, consumerPkg'⟩

end BEDC.Derived.DyadicApproximationUp
