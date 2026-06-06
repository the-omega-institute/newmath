import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathNormalizationObstructionSourceOrder [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName normalizationRead obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont strongNorm normalForm normalizationRead →
        Cont handoff obstruction obstructionRead →
          UnaryHistory normalizationRead ∧ UnaryHistory obstructionRead ∧
            hsame transport localName ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory hsame PkgSig
  intro packet strongNormNormalFormRead handoffObstructionRead
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    transportLocalName, provenancePkg⟩ := packet
  have normalizationUnary : UnaryHistory normalizationRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormNormalFormRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionRead
  exact ⟨normalizationUnary, obstructionReadUnary, transportLocalName, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
