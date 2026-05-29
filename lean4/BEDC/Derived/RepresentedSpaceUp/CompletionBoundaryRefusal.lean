import BEDC.Derived.RepresentedSpaceUp

namespace BEDC.Derived.RepresentedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentedSpaceCarrier_completion_boundary_refusal [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay provenance
        localName bundle pkg →
      Cont target provenance completionRead →
        PkgSig bundle completionRead pkg →
          UnaryHistory name ∧ UnaryHistory schedule ∧ UnaryHistory relation ∧
            UnaryHistory target ∧ UnaryHistory completionRead ∧
              Cont relation target transport ∧ Cont target provenance completionRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier completionRoute completionPkg
  obtain ⟨nameUnary, scheduleUnary, relationUnary, targetUnary, _transportUnary,
    _replayUnary, provenanceUnary, _localNameUnary, _nameScheduleReplay,
    relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed targetUnary provenanceUnary completionRoute
  exact
    ⟨nameUnary, scheduleUnary, relationUnary, targetUnary, completionUnary,
      relationTargetTransport, completionRoute, provenancePkg, completionPkg⟩

end BEDC.Derived.RepresentedSpaceUp
