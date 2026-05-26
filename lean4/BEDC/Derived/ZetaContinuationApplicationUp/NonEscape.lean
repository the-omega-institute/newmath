import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_non_escape [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont application replay downstreamRead →
        PkgSig bundle downstreamRead pkg →
          UnaryHistory eta ∧ UnaryHistory functional ∧ UnaryHistory pole ∧
            UnaryHistory zeroLedger ∧ UnaryHistory gamma ∧ UnaryHistory application ∧
              UnaryHistory downstreamRead ∧ Cont eta functional application ∧
                Cont gamma application replay ∧ Cont application replay downstreamRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier applicationReplayDownstream downstreamReadPkg
  obtain ⟨etaUnary, functionalUnary, poleUnary, zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    _transportReplayProvenance, etaFunctionalApplication, gammaApplicationReplay, provenancePkg,
    _namePkg⟩ := carrier
  have downstreamReadUnary : UnaryHistory downstreamRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayDownstream
  exact
    ⟨etaUnary, functionalUnary, poleUnary, zeroLedgerUnary, gammaUnary, applicationUnary,
      downstreamReadUnary, etaFunctionalApplication, gammaApplicationReplay,
      applicationReplayDownstream, provenancePkg, downstreamReadPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
