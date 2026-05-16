import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICCriticalPathPacket [AskSetup] [PackageSetup]
    (strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory strongNorm ∧ UnaryHistory normalForm ∧ UnaryHistory obstruction ∧
    UnaryHistory handoff ∧ UnaryHistory dischargeSocket ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont strongNorm normalForm route ∧ Cont handoff obstruction dischargeSocket ∧
          hsame transport localName ∧ PkgSig bundle provenance pkg

theorem MetaCICCriticalPathPacket_consistency_handoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont strongNorm normalForm route ∧ hsame transport localName ∧
        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig ProbeBundle UnaryHistory
  intro packet
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _socketUnary, _transportUnary, _routeUnary, _provenanceUnary, _localNameUnary,
    strongNormNormalFormRoute, _handoffObstructionSocket, transportLocalName,
    provenancePkg⟩ := packet
  exact ⟨strongNormNormalFormRoute, transportLocalName, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
