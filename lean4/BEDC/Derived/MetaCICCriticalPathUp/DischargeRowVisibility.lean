import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_discharge_row_visibility [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName socketReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont handoff obstruction socketReplay ->
        hsame socketReplay dischargeSocket ->
          UnaryHistory dischargeSocket ∧ UnaryHistory socketReplay ∧
            Cont handoff obstruction socketReplay ∧ hsame socketReplay dischargeSocket ∧
              hsame transport localName ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: MetaCICCriticalPathPacket BHist ProbeBundle Pkg Cont hsame
  intro packet handoffObstructionReplay replaySocket
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    transportLocalName, provenancePkg⟩ := packet
  have socketReplayUnary : UnaryHistory socketReplay :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionReplay
  exact
    ⟨dischargeSocketUnary, socketReplayUnary, handoffObstructionReplay, replaySocket,
      transportLocalName, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
