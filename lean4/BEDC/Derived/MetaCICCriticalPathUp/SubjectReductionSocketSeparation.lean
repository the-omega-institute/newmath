import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathSubjectReductionSocketSeparation [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName socketRead frontier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont handoff obstruction socketRead ->
        Cont route localName frontier ->
          PkgSig bundle socketRead pkg ->
            PkgSig bundle frontier pkg ->
              UnaryHistory obstruction ∧ UnaryHistory dischargeSocket ∧
                UnaryHistory socketRead ∧ UnaryHistory frontier ∧
                  Cont handoff obstruction socketRead ∧ Cont route localName frontier ∧
                    hsame transport localName ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle socketRead pkg ∧ PkgSig bundle frontier pkg := by
  -- BEDC touchpoint anchor: MetaCICCriticalPathPacket BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro packet handoffObstructionSocket routeLocalNameFrontier socketPkg frontierPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionDischargeSocket, transportLocalName,
    provenancePkg⟩ := packet
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionSocket
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameFrontier
  exact
    ⟨obstructionUnary, dischargeSocketUnary, socketUnary, frontierUnary,
      handoffObstructionSocket, routeLocalNameFrontier, transportLocalName, provenancePkg,
      socketPkg, frontierPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
