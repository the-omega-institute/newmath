import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.Derived.MetaCICCriticalPathUp.DownstreamReadinessBoundary
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem MetaCICCriticalPathPacket_downstream_discharge_visibility [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName downstream socketReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont route localName downstream ->
        PkgSig bundle downstream pkg ->
          Cont handoff obstruction socketReplay ->
            hsame socketReplay dischargeSocket ->
              SemanticNameCert
                  (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
                  (fun row : BHist =>
                    Cont strongNorm normalForm route ∧ Cont handoff obstruction dischargeSocket ∧
                      (hsame row route ∨ hsame row localName ∨ hsame row downstream))
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle downstream pkg)
                  hsame ∧
                UnaryHistory dischargeSocket ∧ UnaryHistory socketReplay ∧
                  Cont handoff obstruction socketReplay ∧ hsame socketReplay dischargeSocket ∧
                    PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameDownstream downstreamPkg handoffObstructionReplay replaySocket
  have downstreamReadiness :=
    MetaCICCriticalPathPacket_downstream_readiness_boundary packet routeLocalNameDownstream
      downstreamPkg
  have dischargeVisibility :=
    MetaCICCriticalPathPacket_discharge_row_visibility packet handoffObstructionReplay replaySocket
  exact
    ⟨downstreamReadiness.left, dischargeVisibility.left, dischargeVisibility.right.left,
      dischargeVisibility.right.right.left, dischargeVisibility.right.right.right.left,
      downstreamReadiness.right⟩

end BEDC.Derived.MetaCICCriticalPathUp
