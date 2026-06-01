import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_normalization_obstruction_route_coverage
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName budget schedule readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont route localName budget ->
        Cont budget route schedule ->
          Cont schedule normalForm readback ->
            PkgSig bundle readback pkg ->
              UnaryHistory obstruction ∧ UnaryHistory route ∧ UnaryHistory budget ∧
                UnaryHistory schedule ∧ UnaryHistory readback ∧
                  Cont strongNorm normalForm route ∧ Cont route localName budget ∧
                    Cont budget route schedule ∧ Cont schedule normalForm readback ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet routeLocalNameBudget budgetRouteSchedule scheduleNormalFormReadback
    readbackPkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have budgetUnary : UnaryHistory budget :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameBudget
  have scheduleUnary : UnaryHistory schedule :=
    unary_cont_closed budgetUnary routeUnary budgetRouteSchedule
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed scheduleUnary normalFormUnary scheduleNormalFormReadback
  exact
    ⟨obstructionUnary, routeUnary, budgetUnary, scheduleUnary, readbackUnary,
      strongNormNormalFormRoute, routeLocalNameBudget, budgetRouteSchedule,
      scheduleNormalFormReadback, provenancePkg, readbackPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
