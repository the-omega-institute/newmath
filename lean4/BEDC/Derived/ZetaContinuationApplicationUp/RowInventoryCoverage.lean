import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_row_inventory_coverage [AskSetup]
    [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      etaFunctionalRead gammaApplicationRead applicationReplayRead ledgerRoute inventoryRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg ->
      Cont eta functional etaFunctionalRead ->
        Cont gamma application gammaApplicationRead ->
          Cont application replay applicationReplayRead ->
            Cont provenance name ledgerRoute ->
              Cont etaFunctionalRead ledgerRoute inventoryRead ->
                PkgSig bundle inventoryRead pkg ->
                  UnaryHistory etaFunctionalRead ∧ UnaryHistory gammaApplicationRead ∧
                    UnaryHistory applicationReplayRead ∧ UnaryHistory ledgerRoute ∧
                      UnaryHistory inventoryRead ∧ Cont eta functional etaFunctionalRead ∧
                        Cont gamma application gammaApplicationRead ∧
                          Cont application replay applicationReplayRead ∧
                            Cont provenance name ledgerRoute ∧
                              Cont etaFunctionalRead ledgerRoute inventoryRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle inventoryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier etaFunctionalRoute gammaApplicationRoute applicationReplayRoute ledgerRouteCont
    inventoryRoute inventoryPkg
  obtain ⟨etaUnary, functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, provenanceUnary, nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have etaFunctionalUnary : UnaryHistory etaFunctionalRead :=
    unary_cont_closed etaUnary functionalUnary etaFunctionalRoute
  have gammaApplicationUnary : UnaryHistory gammaApplicationRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRoute
  have applicationReplayUnary : UnaryHistory applicationReplayRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayRoute
  have ledgerRouteUnary : UnaryHistory ledgerRoute :=
    unary_cont_closed provenanceUnary nameUnary ledgerRouteCont
  have inventoryUnary : UnaryHistory inventoryRead :=
    unary_cont_closed etaFunctionalUnary ledgerRouteUnary inventoryRoute
  exact
    ⟨etaFunctionalUnary, gammaApplicationUnary, applicationReplayUnary, ledgerRouteUnary,
      inventoryUnary, etaFunctionalRoute, gammaApplicationRoute, applicationReplayRoute,
      ledgerRouteCont, inventoryRoute, provenancePkg, inventoryPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
