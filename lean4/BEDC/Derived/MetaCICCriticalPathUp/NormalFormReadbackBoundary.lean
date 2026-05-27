import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_normal_form_readback_boundary [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont strongNorm normalForm readback →
        hsame readback normalForm →
          Cont strongNorm normalForm readback ∧ hsame readback normalForm ∧
            UnaryHistory strongNorm ∧ UnaryHistory normalForm ∧ UnaryHistory obstruction ∧
              UnaryHistory dischargeSocket ∧ hsame transport localName ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro packet strongNormNormalFormReadback readbackNormalForm
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    transportLocalName, provenancePkg⟩ := packet
  exact
    ⟨strongNormNormalFormReadback, readbackNormalForm, strongNormUnary, normalFormUnary,
      obstructionUnary, dischargeSocketUnary, transportLocalName, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
