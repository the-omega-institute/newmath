import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_normalization_source_visibility [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName sourceRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      hsame sourceRead strongNorm →
        Cont sourceRead normalForm endpoint →
          UnaryHistory sourceRead ∧ UnaryHistory normalForm ∧ UnaryHistory endpoint ∧
            Cont sourceRead normalForm endpoint ∧ hsame transport localName ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory hsame PkgSig
  intro packet sourceStrongNorm sourceNormalEndpoint
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    transportLocalName, provenancePkg⟩ := packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_transport strongNormUnary (hsame_symm sourceStrongNorm)
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sourceUnary normalFormUnary sourceNormalEndpoint
  exact
    ⟨sourceUnary, normalFormUnary, endpointUnary, sourceNormalEndpoint,
      transportLocalName, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
