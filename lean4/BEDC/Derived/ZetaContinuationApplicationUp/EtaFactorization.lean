import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_eta_factorization [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      etaRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application
        transport replay provenance name bundle pkg →
      Cont eta application etaRead →
        PkgSig bundle etaRead pkg →
          UnaryHistory eta ∧ UnaryHistory application ∧ UnaryHistory etaRead ∧
            Cont eta application etaRead ∧ Cont eta functional application ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle etaRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier etaApplicationRead etaReadPkg
  obtain ⟨etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, _gammaUnary,
    applicationUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _transportReplayProvenance, etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have etaReadUnary : UnaryHistory etaRead :=
    unary_cont_closed etaUnary applicationUnary etaApplicationRead
  exact
    ⟨etaUnary, applicationUnary, etaReadUnary, etaApplicationRead,
      etaFunctionalApplication, provenancePkg, etaReadPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
