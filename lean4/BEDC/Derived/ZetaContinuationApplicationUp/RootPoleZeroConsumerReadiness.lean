import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_root_pole_zero_consumer_readiness [AskSetup]
    [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name poleRead
      zeroRead ledgerRead poleZeroRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont pole zeroLedger poleRead →
        Cont zeroLedger gamma zeroRead →
          Cont poleRead zeroRead ledgerRead →
            Cont ledgerRead application poleZeroRead →
              PkgSig bundle poleZeroRead pkg →
                UnaryHistory pole ∧ UnaryHistory zeroLedger ∧ UnaryHistory gamma ∧
                  UnaryHistory application ∧ UnaryHistory poleRead ∧ UnaryHistory zeroRead ∧
                    UnaryHistory ledgerRead ∧ UnaryHistory poleZeroRead ∧
                      Cont pole zeroLedger poleRead ∧ Cont zeroLedger gamma zeroRead ∧
                        Cont poleRead zeroRead ledgerRead ∧
                          Cont ledgerRead application poleZeroRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                              PkgSig bundle poleZeroRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier poleZeroLedger zeroGammaRead poleZeroLedgerRead ledgerApplicationRead poleZeroPkg
  obtain ⟨_etaUnary, _functionalUnary, poleUnary, zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, namePkg⟩ := carrier
  have poleReadUnary : UnaryHistory poleRead :=
    unary_cont_closed poleUnary zeroLedgerUnary poleZeroLedger
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed zeroLedgerUnary gammaUnary zeroGammaRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed poleReadUnary zeroReadUnary poleZeroLedgerRead
  have poleZeroReadUnary : UnaryHistory poleZeroRead :=
    unary_cont_closed ledgerReadUnary applicationUnary ledgerApplicationRead
  exact
    ⟨poleUnary, zeroLedgerUnary, gammaUnary, applicationUnary, poleReadUnary,
      zeroReadUnary, ledgerReadUnary, poleZeroReadUnary, poleZeroLedger, zeroGammaRead,
      poleZeroLedgerRead, ledgerApplicationRead, provenancePkg, namePkg, poleZeroPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
