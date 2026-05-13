import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_finite_packet_terminal_selector_determinacy
    [AskSetup] [PackageSetup]
    {precisionA endpointA windowA ledgerA provenanceA precisionB endpointB windowB ledgerB
      provenanceB commonPrecision commonEndpoint commonWindow commonLedger commonProvenance
      meshCell enclosure sealA sealB readA readB selectorA selectorB : BHist}
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
                              Cont meshCell commonProvenance enclosure ->
                                Cont commonLedger commonProvenance sealA ->
                                  Cont commonLedger commonProvenance sealB ->
                                    Cont enclosure sealA readA ->
                                      Cont enclosure sealB readB ->
                                        Cont commonWindow commonProvenance selectorA ->
                                          Cont commonWindow commonProvenance selectorB ->
                                            PkgSig bundle meshCell pkg ->
                                              PkgSig bundle enclosure pkg ->
                                                PkgSig bundle sealA pkg ->
                                                  PkgSig bundle sealB pkg ->
                                                    PkgSig bundle readA pkg ->
                                                      PkgSig bundle readB pkg ->
                                                        DyadicApproximationCarrier
                                                            commonPrecision commonEndpoint
                                                            commonWindow commonLedger
                                                            commonProvenance bundle pkg ∧
                                                          UnaryHistory selectorA ∧
                                                            UnaryHistory selectorB ∧
                                                              hsame selectorA selectorB ∧
                                                                hsame sealA sealB ∧
                                                                  UnaryHistory readA ∧
                                                                    UnaryHistory readB := by
  intro carrierA carrierB samePrecisionA samePrecisionB sameEndpointA sameEndpointB
  intro sameLedgerA sameLedgerB sameProvenanceA sameProvenanceB
  intro commonPrecisionEndpointWindow commonWindowLedgerProvenance
  intro commonWindowProvenanceMesh meshProvenanceEnclosure
  intro commonLedgerProvenanceSealA commonLedgerProvenanceSealB
  intro enclosureSealReadA enclosureSealReadB
  intro commonWindowProvenanceSelectorA commonWindowProvenanceSelectorB
  intro _meshPkg _enclosurePkg _sealAPkg _sealBPkg _readAPkg _readBPkg
  have refined :
      DyadicApproximationCarrier commonPrecision commonEndpoint commonWindow commonLedger
          commonProvenance bundle pkg ∧
        hsame windowA commonWindow ∧ hsame windowB commonWindow :=
    DyadicApproximationCarrier_common_precision_refinement carrierA carrierB
      samePrecisionA samePrecisionB sameEndpointA sameEndpointB sameLedgerA sameLedgerB
      sameProvenanceA sameProvenanceB commonPrecisionEndpointWindow
      commonWindowLedgerProvenance
  have commonCarrierProof :
      DyadicApproximationCarrier commonPrecision commonEndpoint commonWindow commonLedger
          commonProvenance bundle pkg :=
    refined.left
  obtain ⟨commonCarrier, _sameWindowA, _sameWindowB⟩ := refined
  obtain ⟨_commonPrecisionUnary, _commonEndpointUnary, commonWindowUnary,
    commonLedgerUnary, commonProvenanceUnary, _commonPrecisionEndpointWindow,
    _commonWindowLedgerProvenance, _commonPkg⟩ := commonCarrier
  have meshUnary : UnaryHistory meshCell :=
    unary_cont_closed commonWindowUnary commonProvenanceUnary commonWindowProvenanceMesh
  have enclosureUnary : UnaryHistory enclosure :=
    unary_cont_closed meshUnary commonProvenanceUnary meshProvenanceEnclosure
  have sealAUnary : UnaryHistory sealA :=
    unary_cont_closed commonLedgerUnary commonProvenanceUnary commonLedgerProvenanceSealA
  have sealBUnary : UnaryHistory sealB :=
    unary_cont_closed commonLedgerUnary commonProvenanceUnary commonLedgerProvenanceSealB
  have readAUnary : UnaryHistory readA :=
    unary_cont_closed enclosureUnary sealAUnary enclosureSealReadA
  have readBUnary : UnaryHistory readB :=
    unary_cont_closed enclosureUnary sealBUnary enclosureSealReadB
  have selectorAUnary : UnaryHistory selectorA :=
    unary_cont_closed commonWindowUnary commonProvenanceUnary commonWindowProvenanceSelectorA
  have selectorBUnary : UnaryHistory selectorB :=
    unary_cont_closed commonWindowUnary commonProvenanceUnary commonWindowProvenanceSelectorB
  have sameSelector : hsame selectorA selectorB :=
    cont_deterministic commonWindowProvenanceSelectorA commonWindowProvenanceSelectorB
  have sameSeal : hsame sealA sealB :=
    cont_deterministic commonLedgerProvenanceSealA commonLedgerProvenanceSealB
  exact
    ⟨commonCarrierProof, selectorAUnary, selectorBUnary, sameSelector, sameSeal, readAUnary,
      readBUnary⟩

end BEDC.Derived.DyadicApproximationUp
