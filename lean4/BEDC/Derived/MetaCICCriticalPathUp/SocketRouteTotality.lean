import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_socket_route_totality [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont handoff obstruction socketRead →
        PkgSig bundle socketRead pkg →
          UnaryHistory strongNorm ∧ UnaryHistory normalForm ∧ UnaryHistory obstruction ∧
            UnaryHistory handoff ∧ UnaryHistory dischargeSocket ∧ UnaryHistory socketRead ∧
              Cont strongNorm normalForm route ∧ Cont handoff obstruction socketRead ∧
                hsame transport localName ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle socketRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame
  intro packet handoffObstructionRead socketReadPkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, strongNormNormalFormRoute, _handoffObstructionSocket,
    transportLocalName, provenancePkg⟩ := packet
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionRead
  exact
    ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
      dischargeSocketUnary, socketReadUnary, strongNormNormalFormRoute,
      handoffObstructionRead, transportLocalName, provenancePkg, socketReadPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
