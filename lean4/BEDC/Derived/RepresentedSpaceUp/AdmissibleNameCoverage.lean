import BEDC.Derived.RepresentedSpaceUp

namespace BEDC.Derived.RepresentedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentedSpaceCarrier_admissible_name_coverage [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName scheduleRead targetRead
      covered : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
        provenance localName bundle pkg →
      Cont name schedule scheduleRead →
        Cont relation target targetRead →
          Cont scheduleRead targetRead covered →
            PkgSig bundle covered pkg →
              UnaryHistory name ∧ UnaryHistory schedule ∧ UnaryHistory relation ∧
                UnaryHistory target ∧ UnaryHistory scheduleRead ∧ UnaryHistory targetRead ∧
                  UnaryHistory covered ∧ Cont name schedule scheduleRead ∧
                    Cont relation target targetRead ∧ Cont scheduleRead targetRead covered ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle covered pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier nameScheduleRead relationTargetRead coveredRead coveredPkg
  obtain ⟨nameUnary, scheduleUnary, relationUnary, targetUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have scheduleReadUnary : UnaryHistory scheduleRead :=
    unary_cont_closed nameUnary scheduleUnary nameScheduleRead
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed relationUnary targetUnary relationTargetRead
  have coveredUnary : UnaryHistory covered :=
    unary_cont_closed scheduleReadUnary targetReadUnary coveredRead
  exact
    ⟨nameUnary, scheduleUnary, relationUnary, targetUnary, scheduleReadUnary,
      targetReadUnary, coveredUnary, nameScheduleRead, relationTargetRead, coveredRead,
      provenancePkg, coveredPkg⟩

end BEDC.Derived.RepresentedSpaceUp
