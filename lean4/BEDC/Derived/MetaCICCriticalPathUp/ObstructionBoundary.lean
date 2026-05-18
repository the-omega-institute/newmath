import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_obstruction_boundary [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      UnaryHistory obstruction ∧ UnaryHistory handoff ∧ UnaryHistory dischargeSocket ∧
        Cont handoff obstruction dischargeSocket ∧ hsame transport localName ∧
          PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro packet
  rcases packet with
    ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
      dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
      _localNameUnary, _strongNormNormalFormRoute, handoffObstructionSocket,
      transportLocalName, provenancePkg⟩
  exact
    ⟨obstructionUnary, handoffUnary, dischargeSocketUnary, handoffObstructionSocket,
      transportLocalName, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
