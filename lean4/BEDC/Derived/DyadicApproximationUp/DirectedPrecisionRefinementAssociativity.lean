import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_directed_precision_refinement_associativity
    [AskSetup] [PackageSetup]
    {precisionA endpointA windowA ledgerA provenanceA precisionB endpointB windowB ledgerB
      provenanceB precisionC endpointC windowC ledgerC provenanceC commonPrecision
      commonEndpoint commonWindow commonLedger commonProvenance sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precisionA endpointA windowA ledgerA provenanceA bundle pkg ->
      DyadicApproximationCarrier precisionB endpointB windowB ledgerB provenanceB bundle pkg ->
        DyadicApproximationCarrier precisionC endpointC windowC ledgerC provenanceC bundle pkg ->
          hsame precisionA commonPrecision ->
            hsame precisionB commonPrecision ->
              hsame precisionC commonPrecision ->
                hsame endpointA commonEndpoint ->
                  hsame endpointB commonEndpoint ->
                    hsame endpointC commonEndpoint ->
                      hsame ledgerA commonLedger ->
                        hsame ledgerB commonLedger ->
                          hsame ledgerC commonLedger ->
                            hsame provenanceA commonProvenance ->
                              hsame provenanceB commonProvenance ->
                                hsame provenanceC commonProvenance ->
                                  Cont commonPrecision commonEndpoint commonWindow ->
                                    Cont commonWindow commonLedger commonProvenance ->
                                      Cont commonLedger commonProvenance sealRead ->
                                        PkgSig bundle sealRead pkg ->
                                          DyadicApproximationCarrier commonPrecision
                                              commonEndpoint commonWindow commonLedger
                                              commonProvenance bundle pkg ∧
                                            UnaryHistory sealRead ∧ hsame windowA commonWindow ∧
                                              hsame windowB commonWindow ∧
                                                hsame windowC commonWindow := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrierA carrierB carrierC samePrecisionA samePrecisionB samePrecisionC
  intro sameEndpointA sameEndpointB sameEndpointC sameLedgerA sameLedgerB sameLedgerC
  intro sameProvenanceA sameProvenanceB sameProvenanceC
  intro commonPrecisionEndpointWindow commonWindowLedgerProvenance commonLedgerProvenanceSeal
  intro _sealPkg
  have pairRefinement :
      DyadicApproximationCarrier commonPrecision commonEndpoint commonWindow commonLedger
          commonProvenance bundle pkg ∧
        hsame windowA commonWindow ∧ hsame windowB commonWindow :=
    DyadicApproximationCarrier_common_precision_refinement carrierA carrierB samePrecisionA
      samePrecisionB sameEndpointA sameEndpointB sameLedgerA sameLedgerB sameProvenanceA
      sameProvenanceB commonPrecisionEndpointWindow commonWindowLedgerProvenance
  have commonCarrier :
      DyadicApproximationCarrier commonPrecision commonEndpoint commonWindow commonLedger
        commonProvenance bundle pkg :=
    pairRefinement.left
  have sameWindowA : hsame windowA commonWindow :=
    pairRefinement.right.left
  have sameWindowB : hsame windowB commonWindow :=
    pairRefinement.right.right
  have terminalRefinement :
      DyadicApproximationCarrier commonPrecision commonEndpoint commonWindow commonLedger
          commonProvenance bundle pkg ∧
        hsame commonWindow commonWindow ∧ hsame windowC commonWindow :=
    DyadicApproximationCarrier_common_precision_refinement commonCarrier carrierC
      (hsame_refl commonPrecision) samePrecisionC (hsame_refl commonEndpoint) sameEndpointC
      (hsame_refl commonLedger) sameLedgerC (hsame_refl commonProvenance) sameProvenanceC
      commonPrecisionEndpointWindow commonWindowLedgerProvenance
  have terminalCarrier :
      DyadicApproximationCarrier commonPrecision commonEndpoint commonWindow commonLedger
        commonProvenance bundle pkg :=
    terminalRefinement.left
  have sameWindowC : hsame windowC commonWindow :=
    terminalRefinement.right.right
  obtain ⟨_precisionUnary, _endpointUnary, _windowUnary, ledgerUnary, provenanceUnary,
    _precisionEndpointWindow, _windowLedgerProvenance, _pkgSig⟩ := terminalCarrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerUnary provenanceUnary commonLedgerProvenanceSeal
  exact ⟨terminalRefinement.left, sealReadUnary, sameWindowA, sameWindowB, sameWindowC⟩

end BEDC.Derived.DyadicApproximationUp
