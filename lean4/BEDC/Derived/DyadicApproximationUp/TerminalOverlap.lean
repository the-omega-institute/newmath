import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_overlap_directed_seal_exhaustion
    [AskSetup] [PackageSetup]
    {precisionA endpointA windowA ledgerA provenanceA precisionB endpointB windowB ledgerB
      provenanceB commonPrecision commonEndpoint commonWindow commonLedger commonProvenance sealA
      sealB sourceRead overlapBoundary : BHist}
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
                            Cont commonLedger commonProvenance sealA ->
                              Cont commonLedger commonProvenance sealB ->
                                Cont commonWindow commonProvenance sourceRead ->
                                  Cont sourceRead sealA overlapBoundary ->
                                    PkgSig bundle sourceRead pkg ->
                                      PkgSig bundle overlapBoundary pkg ->
                                        DyadicApproximationCarrier commonPrecision
                                            commonEndpoint commonWindow commonLedger
                                            commonProvenance bundle pkg ∧
                                          UnaryHistory sealA ∧ UnaryHistory sealB ∧
                                            UnaryHistory sourceRead ∧
                                              UnaryHistory overlapBoundary ∧
                                                hsame sealA sealB ∧
                                                  PkgSig bundle overlapBoundary pkg := by
  intro carrierA carrierB samePrecisionA samePrecisionB sameEndpointA sameEndpointB
  intro sameLedgerA sameLedgerB sameProvenanceA sameProvenanceB
  intro commonPrecisionEndpointWindow commonWindowLedgerProvenance
  intro commonLedgerProvenanceSealA commonLedgerProvenanceSealB
  intro commonWindowProvenanceSource sourceSealBoundary _sourcePkg boundaryPkg
  have refined :
      DyadicApproximationCarrier commonPrecision commonEndpoint commonWindow commonLedger
          commonProvenance bundle pkg ∧
        hsame windowA commonWindow ∧ hsame windowB commonWindow :=
    DyadicApproximationCarrier_common_precision_refinement carrierA carrierB
      samePrecisionA samePrecisionB sameEndpointA sameEndpointB sameLedgerA sameLedgerB
      sameProvenanceA sameProvenanceB commonPrecisionEndpointWindow
      commonWindowLedgerProvenance
  obtain ⟨commonCarrier, _sameWindowA, _sameWindowB⟩ := refined
  have commonCarrierPacked :
      DyadicApproximationCarrier commonPrecision commonEndpoint commonWindow commonLedger
          commonProvenance bundle pkg :=
    commonCarrier
  obtain ⟨_precisionUnary, _endpointUnary, commonWindowUnary, commonLedgerUnary,
    commonProvenanceUnary, _precisionEndpointWindow, _windowLedgerProvenance,
    _provenancePkg⟩ := commonCarrier
  have sealAUnary : UnaryHistory sealA :=
    unary_cont_closed commonLedgerUnary commonProvenanceUnary commonLedgerProvenanceSealA
  have sealBUnary : UnaryHistory sealB :=
    unary_cont_closed commonLedgerUnary commonProvenanceUnary commonLedgerProvenanceSealB
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed commonWindowUnary commonProvenanceUnary commonWindowProvenanceSource
  have overlapBoundaryUnary : UnaryHistory overlapBoundary :=
    unary_cont_closed sourceReadUnary sealAUnary sourceSealBoundary
  have sameSeals : hsame sealA sealB :=
    cont_deterministic commonLedgerProvenanceSealA commonLedgerProvenanceSealB
  exact
    ⟨commonCarrierPacked, sealAUnary, sealBUnary, sourceReadUnary, overlapBoundaryUnary,
      sameSeals, boundaryPkg⟩

theorem DyadicApproximationCarrier_overlap_seal_idempotence
    [AskSetup] [PackageSetup]
    {precisionA endpointA windowA ledgerA provenanceA precisionB endpointB windowB ledgerB
      provenanceB commonPrecision commonEndpoint commonWindow commonLedger commonProvenance sealA
      sealB sourceRead firstBoundary secondBoundary reread : BHist}
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
                            Cont commonLedger commonProvenance sealA ->
                              Cont commonLedger commonProvenance sealB ->
                                Cont commonWindow commonProvenance sourceRead ->
                                  Cont sourceRead sealA firstBoundary ->
                                    Cont firstBoundary sealB secondBoundary ->
                                      Cont sourceRead sealA reread ->
                                        PkgSig bundle firstBoundary pkg ->
                                          PkgSig bundle secondBoundary pkg ->
                                            DyadicApproximationCarrier commonPrecision
                                                commonEndpoint commonWindow commonLedger
                                                commonProvenance bundle pkg ∧
                                              UnaryHistory firstBoundary ∧
                                                UnaryHistory secondBoundary ∧
                                                  UnaryHistory reread ∧
                                                    hsame firstBoundary reread ∧
                                                      PkgSig bundle secondBoundary pkg := by
  intro carrierA carrierB samePrecisionA samePrecisionB sameEndpointA sameEndpointB
  intro sameLedgerA sameLedgerB sameProvenanceA sameProvenanceB
  intro commonPrecisionEndpointWindow commonWindowLedgerProvenance
  intro commonLedgerProvenanceSealA commonLedgerProvenanceSealB
  intro commonWindowProvenanceSource sourceSealFirst firstSealSecond sourceSealReread
  intro _firstBoundaryPkg secondBoundaryPkg
  have refined :
      DyadicApproximationCarrier commonPrecision commonEndpoint commonWindow commonLedger
          commonProvenance bundle pkg ∧
        hsame windowA commonWindow ∧ hsame windowB commonWindow :=
    DyadicApproximationCarrier_common_precision_refinement carrierA carrierB
      samePrecisionA samePrecisionB sameEndpointA sameEndpointB sameLedgerA sameLedgerB
      sameProvenanceA sameProvenanceB commonPrecisionEndpointWindow
      commonWindowLedgerProvenance
  obtain ⟨commonCarrier, _sameWindowA, _sameWindowB⟩ := refined
  have commonCarrierPacked :
      DyadicApproximationCarrier commonPrecision commonEndpoint commonWindow commonLedger
          commonProvenance bundle pkg :=
    commonCarrier
  obtain ⟨_precisionUnary, _endpointUnary, commonWindowUnary, commonLedgerUnary,
    commonProvenanceUnary, _precisionEndpointWindow, _windowLedgerProvenance,
    _provenancePkg⟩ := commonCarrier
  have sealAUnary : UnaryHistory sealA :=
    unary_cont_closed commonLedgerUnary commonProvenanceUnary commonLedgerProvenanceSealA
  have sealBUnary : UnaryHistory sealB :=
    unary_cont_closed commonLedgerUnary commonProvenanceUnary commonLedgerProvenanceSealB
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed commonWindowUnary commonProvenanceUnary commonWindowProvenanceSource
  have firstBoundaryUnary : UnaryHistory firstBoundary :=
    unary_cont_closed sourceReadUnary sealAUnary sourceSealFirst
  have secondBoundaryUnary : UnaryHistory secondBoundary :=
    unary_cont_closed firstBoundaryUnary sealBUnary firstSealSecond
  have rereadUnary : UnaryHistory reread :=
    unary_cont_closed sourceReadUnary sealAUnary sourceSealReread
  have sameFirstReread : hsame firstBoundary reread :=
    cont_deterministic sourceSealFirst sourceSealReread
  exact
    ⟨commonCarrierPacked, firstBoundaryUnary, secondBoundaryUnary, rereadUnary,
      sameFirstReread, secondBoundaryPkg⟩

theorem DyadicApproximationCarrier_window_regseqrat_source_exhaustion
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint
      terminalWindow terminalLedger terminalProvenance sealRow regseqRead
      intervalContainment : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision terminalPrecision ->
        hsame endpoint terminalEndpoint ->
          hsame ledger terminalLedger ->
            hsame provenance terminalProvenance ->
              Cont terminalPrecision terminalEndpoint terminalWindow ->
                Cont terminalWindow terminalLedger terminalProvenance ->
                  Cont terminalWindow terminalProvenance regseqRead ->
                    Cont terminalLedger terminalProvenance sealRow ->
                      Cont terminalEndpoint regseqRead intervalContainment ->
                        PkgSig bundle regseqRead pkg ->
                          PkgSig bundle sealRow pkg ->
                            PkgSig bundle intervalContainment pkg ->
                              DyadicApproximationCarrier terminalPrecision terminalEndpoint
                                  terminalWindow terminalLedger terminalProvenance bundle pkg ∧
                                UnaryHistory regseqRead ∧ UnaryHistory sealRow ∧
                                  UnaryHistory intervalContainment ∧
                                    hsame window terminalWindow ∧
                                      PkgSig bundle regseqRead pkg ∧
                                        PkgSig bundle sealRow pkg ∧
                                          PkgSig bundle intervalContainment pkg := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
  intro terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  intro terminalWindowProvenanceRead terminalLedgerProvenanceSeal
  intro terminalEndpointReadContainment readPkg sealPkg containmentPkg
  have transported :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        hsame window terminalWindow :=
    DyadicApproximationCarrier_classifier_transport carrier samePrecision sameEndpoint
      sameLedger sameProvenance terminalPrecisionEndpointWindow
      terminalWindowLedgerProvenance
  obtain ⟨terminalCarrier, sameWindow⟩ := transported
  obtain ⟨_terminalPrecisionUnary, terminalEndpointUnary, terminalWindowUnary,
    terminalLedgerUnary, terminalProvenanceUnary, _terminalPrecisionEndpointWindow,
    _terminalWindowLedgerProvenance, _terminalProvenancePkg⟩ := terminalCarrier
  have readUnary : UnaryHistory regseqRead :=
    unary_cont_closed terminalWindowUnary terminalProvenanceUnary terminalWindowProvenanceRead
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed terminalLedgerUnary terminalProvenanceUnary terminalLedgerProvenanceSeal
  have containmentUnary : UnaryHistory intervalContainment :=
    unary_cont_closed terminalEndpointUnary readUnary terminalEndpointReadContainment
  exact
    ⟨⟨_terminalPrecisionUnary, terminalEndpointUnary, terminalWindowUnary, terminalLedgerUnary,
        terminalProvenanceUnary, _terminalPrecisionEndpointWindow,
        _terminalWindowLedgerProvenance, _terminalProvenancePkg⟩,
      readUnary, sealUnary, containmentUnary, sameWindow, readPkg, sealPkg, containmentPkg⟩

end BEDC.Derived.DyadicApproximationUp
