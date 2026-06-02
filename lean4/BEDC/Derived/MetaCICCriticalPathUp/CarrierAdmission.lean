import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_carrier_admission [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont obstruction handoff socketRead →
        PkgSig bundle socketRead pkg →
          UnaryHistory strongNorm ∧ UnaryHistory normalForm ∧ UnaryHistory obstruction ∧
            UnaryHistory handoff ∧ UnaryHistory dischargeSocket ∧ UnaryHistory socketRead ∧
              Cont strongNorm normalForm route ∧ Cont obstruction handoff socketRead ∧
                hsame transport localName ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle socketRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro packet obstructionHandoffSocket socketPkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, strongNormNormalFormRoute, _handoffObstructionSocket,
    transportLocalName, provenancePkg⟩ := packet
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed obstructionUnary handoffUnary obstructionHandoffSocket
  exact
    ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
      dischargeSocketUnary, socketReadUnary, strongNormNormalFormRoute,
      obstructionHandoffSocket, transportLocalName, provenancePkg, socketPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
