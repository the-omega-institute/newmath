import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamStartLedgerUniqueness [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont schedule start endpoint →
        PkgSig bundle endpoint pkg →
          hsame endpoint replay ∧ UnaryHistory endpoint ∧ Cont schedule start replay ∧
            Cont schedule start endpoint ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig UnaryHistory
  intro carrier scheduleStartEndpoint endpointPkg
  obtain ⟨_sourceUnary, scheduleUnary, startUnary, replayUnary, _transportUnary,
    _provenanceUnary, _nameUnary, scheduleStartReplay, _sourceReplayProvenance,
    _provenanceReplay, provenancePkg, _namePkg⟩ := carrier
  have endpointReplay : hsame endpoint replay :=
    cont_deterministic scheduleStartEndpoint scheduleStartReplay
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed scheduleUnary startUnary scheduleStartEndpoint
  exact
    ⟨endpointReplay, endpointUnary, scheduleStartReplay, scheduleStartEndpoint, provenancePkg,
      endpointPkg⟩

end BEDC.Derived.HistTimeStreamUp
