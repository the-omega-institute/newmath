import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_root_gamma_operation_handoff [AskSetup]
    [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name gammaRead
      operationRead rootRead poleRead zeroRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont gamma application gammaRead →
        Cont application replay operationRead →
          Cont provenance name rootRead →
            Cont pole zeroLedger poleRead →
              Cont zeroLedger gamma zeroRead →
                PkgSig bundle operationRead pkg →
                  PkgSig bundle rootRead pkg →
                    UnaryHistory gammaRead ∧ UnaryHistory operationRead ∧
                      UnaryHistory rootRead ∧ UnaryHistory poleRead ∧
                        UnaryHistory zeroRead ∧ Cont gamma application gammaRead ∧
                          Cont application replay operationRead ∧ Cont provenance name rootRead ∧
                            Cont pole zeroLedger poleRead ∧ Cont zeroLedger gamma zeroRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle operationRead pkg ∧
                                  PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier gammaApplicationRead applicationReplayOperation provenanceNameRoot
    poleZeroLedgerRead zeroLedgerGammaRead operationPkg rootPkg
  obtain ⟨_etaUnary, _functionalUnary, poleUnary, zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, provenanceUnary, nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayOperation
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameRoot
  have poleReadUnary : UnaryHistory poleRead :=
    unary_cont_closed poleUnary zeroLedgerUnary poleZeroLedgerRead
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed zeroLedgerUnary gammaUnary zeroLedgerGammaRead
  exact
    ⟨gammaReadUnary, operationReadUnary, rootReadUnary, poleReadUnary, zeroReadUnary,
      gammaApplicationRead, applicationReplayOperation, provenanceNameRoot,
      poleZeroLedgerRead, zeroLedgerGammaRead, provenancePkg, operationPkg, rootPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
