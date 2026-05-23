import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_discharge_socket_coverage [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName socketRead frontier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont handoff obstruction socketRead ->
        Cont route localName frontier ->
          PkgSig bundle socketRead pkg ->
            PkgSig bundle frontier pkg ->
              UnaryHistory socketRead ∧ UnaryHistory frontier ∧
                Cont handoff obstruction socketRead ∧ Cont route localName frontier ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle socketRead pkg ∧
                    PkgSig bundle frontier pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet handoffObstructionRead routeLocalNameFrontier socketPkg frontierPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionRead
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameFrontier
  exact
    ⟨socketReadUnary, frontierUnary, handoffObstructionRead, routeLocalNameFrontier,
      provenancePkg, socketPkg, frontierPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
