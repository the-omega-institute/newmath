import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_pole_zero_ledger_separation
    [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      poleRead zeroRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont pole transport poleRead →
        Cont zeroLedger transport zeroRead →
          UnaryHistory pole ∧ UnaryHistory zeroLedger ∧ UnaryHistory poleRead ∧
            UnaryHistory zeroRead ∧ Cont pole transport poleRead ∧
              Cont zeroLedger transport zeroRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier poleTransportRead zeroTransportRead
  obtain ⟨_etaUnary, _functionalUnary, poleUnary, zeroLedgerUnary, _gammaUnary,
    _applicationUnary, transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, namePkg⟩ := carrier
  have poleReadUnary : UnaryHistory poleRead :=
    unary_cont_closed poleUnary transportUnary poleTransportRead
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed zeroLedgerUnary transportUnary zeroTransportRead
  exact
    ⟨poleUnary, zeroLedgerUnary, poleReadUnary, zeroReadUnary, poleTransportRead,
      zeroTransportRead, provenancePkg, namePkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
