import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICParallelDiamondCandidateMediatedSNReadback [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      hsame readback route →
        Cont strongNorm normalForm readback →
          PkgSig bundle provenance pkg →
            UnaryHistory strongNorm ∧ UnaryHistory normalForm ∧ UnaryHistory obstruction ∧
              UnaryHistory dischargeSocket ∧ hsame readback route ∧
                Cont strongNorm normalForm readback ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: MetaCICCriticalPathPacket BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro packet sameReadback readbackRoute provenancePkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _packetProvenancePkg⟩ := packet
  have _readbackUnary : UnaryHistory readback :=
    unary_transport routeUnary (hsame_symm sameReadback)
  exact
    ⟨strongNormUnary, normalFormUnary, obstructionUnary, dischargeSocketUnary,
      sameReadback, readbackRoute, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
