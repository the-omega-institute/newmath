import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_common_refinement_enclosure_handoff
    [AskSetup] [PackageSetup]
    {precisionA endpointA windowA ledgerA provenanceA precisionB endpointB windowB ledgerB
      provenanceB commonPrecision commonEndpoint commonWindow commonLedger commonProvenance
      meshCell validatedEnclosure sealRow realRead : BHist}
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
                                  Cont validatedEnclosure sealRow realRead ->
                                    PkgSig bundle meshCell pkg ->
                                      PkgSig bundle validatedEnclosure pkg ->
                                        PkgSig bundle sealRow pkg ->
                                          PkgSig bundle realRead pkg ->
                                            DyadicApproximationCarrier commonPrecision
                                                commonEndpoint commonWindow commonLedger
                                                commonProvenance bundle pkg ∧
                                              UnaryHistory meshCell ∧
                                                UnaryHistory validatedEnclosure ∧
                                                  UnaryHistory sealRow ∧
                                                    UnaryHistory realRead ∧
                                                      hsame windowA commonWindow ∧
                                                        hsame windowB commonWindow ∧
                                                          PkgSig bundle realRead pkg := by
  intro carrierA carrierB samePrecisionA samePrecisionB sameEndpointA sameEndpointB
  intro sameLedgerA sameLedgerB sameProvenanceA sameProvenanceB
  intro commonPrecisionEndpointWindow commonWindowLedgerProvenance
  intro commonWindowProvenanceMesh meshProvenanceEnclosure commonLedgerProvenanceSeal
  intro enclosureSealRead _meshPkg _enclosurePkg _sealPkg readPkg
  have refined :
      DyadicApproximationCarrier commonPrecision commonEndpoint commonWindow commonLedger
          commonProvenance bundle pkg ∧
        hsame windowA commonWindow ∧ hsame windowB commonWindow :=
    DyadicApproximationCarrier_common_precision_refinement carrierA carrierB
      samePrecisionA samePrecisionB sameEndpointA sameEndpointB sameLedgerA sameLedgerB
      sameProvenanceA sameProvenanceB commonPrecisionEndpointWindow
      commonWindowLedgerProvenance
  rcases refined with ⟨commonCarrier, sameWindowA, sameWindowB⟩
  rcases commonCarrier with
    ⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
      precisionEndpointWindow, windowLedgerProvenance, pkgSig⟩
  have meshUnary : UnaryHistory meshCell :=
    unary_cont_closed windowUnary provenanceUnary commonWindowProvenanceMesh
  have enclosureUnary : UnaryHistory validatedEnclosure :=
    unary_cont_closed meshUnary provenanceUnary meshProvenanceEnclosure
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed ledgerUnary provenanceUnary commonLedgerProvenanceSeal
  have readUnary : UnaryHistory realRead :=
    unary_cont_closed enclosureUnary sealUnary enclosureSealRead
  exact
    ⟨⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
        precisionEndpointWindow, windowLedgerProvenance, pkgSig⟩,
      meshUnary, enclosureUnary, sealUnary, readUnary, sameWindowA, sameWindowB, readPkg⟩

theorem DyadicApproximationCarrier_terminal_window_two_stage_factorization
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance prefixPrecision prefixEndpoint prefixWindow
      prefixLedger prefixProvenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance meshCell validatedEnclosure sealRow consumerSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision prefixPrecision ->
        hsame endpoint prefixEndpoint ->
          hsame ledger prefixLedger ->
            hsame provenance prefixProvenance ->
              Cont prefixPrecision prefixEndpoint prefixWindow ->
                Cont prefixWindow prefixLedger prefixProvenance ->
                  hsame prefixPrecision terminalPrecision ->
                    hsame prefixEndpoint terminalEndpoint ->
                      hsame prefixLedger terminalLedger ->
                        hsame prefixProvenance terminalProvenance ->
                          Cont terminalPrecision terminalEndpoint terminalWindow ->
                            Cont terminalWindow terminalLedger terminalProvenance ->
                              Cont terminalWindow terminalProvenance meshCell ->
                                Cont meshCell terminalProvenance validatedEnclosure ->
                                  Cont terminalLedger terminalProvenance sealRow ->
                                    Cont validatedEnclosure sealRow consumerSurface ->
                                      PkgSig bundle meshCell pkg ->
                                        PkgSig bundle validatedEnclosure pkg ->
                                          PkgSig bundle sealRow pkg ->
                                            PkgSig bundle consumerSurface pkg ->
                                              DyadicApproximationCarrier prefixPrecision
                                                  prefixEndpoint prefixWindow prefixLedger
                                                  prefixProvenance bundle pkg ∧
                                                DyadicApproximationCarrier terminalPrecision
                                                  terminalEndpoint terminalWindow terminalLedger
                                                  terminalProvenance bundle pkg ∧
                                                  UnaryHistory meshCell ∧
                                                    UnaryHistory validatedEnclosure ∧
                                                      UnaryHistory sealRow ∧
                                                        UnaryHistory consumerSurface ∧
                                                          hsame prefixWindow terminalWindow ∧
                                                            PkgSig bundle consumerSurface pkg := by
  intro carrier samePrecisionPrefix sameEndpointPrefix sameLedgerPrefix sameProvenancePrefix
  intro prefixPrecisionEndpointWindow prefixWindowLedgerProvenance samePrefixPrecisionTerminal
  intro samePrefixEndpointTerminal samePrefixLedgerTerminal samePrefixProvenanceTerminal
  intro terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  intro terminalWindowProvenanceMesh meshProvenanceEnclosure terminalLedgerProvenanceSeal
  intro enclosureSealConsumer _meshPkg _enclosurePkg _sealPkg consumerPkg
  have projected :
      DyadicApproximationCarrier prefixPrecision prefixEndpoint prefixWindow prefixLedger
          prefixProvenance bundle pkg ∧
        DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
          UnaryHistory meshCell ∧ hsame prefixWindow terminalWindow :=
    DyadicApproximationCarrier_terminal_window_prefix_projection carrier
      samePrecisionPrefix sameEndpointPrefix sameLedgerPrefix sameProvenancePrefix
      prefixPrecisionEndpointWindow prefixWindowLedgerProvenance samePrefixPrecisionTerminal
      samePrefixEndpointTerminal samePrefixLedgerTerminal samePrefixProvenanceTerminal
      terminalPrecisionEndpointWindow terminalWindowLedgerProvenance terminalWindowProvenanceMesh
  rcases projected with ⟨prefixCarrier, terminalCarrier, meshUnary, samePrefixWindow⟩
  rcases terminalCarrier with
    ⟨terminalPrecisionUnary, terminalEndpointUnary, terminalWindowUnary, terminalLedgerUnary,
      terminalProvenanceUnary, terminalPrecisionEndpointWindow', terminalWindowLedgerProvenance',
      terminalPkg⟩
  have enclosureUnary : UnaryHistory validatedEnclosure :=
    unary_cont_closed meshUnary terminalProvenanceUnary meshProvenanceEnclosure
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed terminalLedgerUnary terminalProvenanceUnary terminalLedgerProvenanceSeal
  have consumerUnary : UnaryHistory consumerSurface :=
    unary_cont_closed enclosureUnary sealUnary enclosureSealConsumer
  exact
    ⟨prefixCarrier,
      ⟨terminalPrecisionUnary, terminalEndpointUnary, terminalWindowUnary, terminalLedgerUnary,
        terminalProvenanceUnary, terminalPrecisionEndpointWindow', terminalWindowLedgerProvenance',
        terminalPkg⟩,
      meshUnary, enclosureUnary, sealUnary, consumerUnary, samePrefixWindow, consumerPkg⟩

end BEDC.Derived.DyadicApproximationUp
