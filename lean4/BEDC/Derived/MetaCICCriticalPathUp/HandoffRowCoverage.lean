import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_handoff_row_coverage [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName handoffRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont handoff obstruction socketRead ->
        Cont handoff localName handoffRead ->
          PkgSig bundle handoffRead pkg ->
            UnaryHistory handoff ∧ UnaryHistory obstruction ∧ UnaryHistory dischargeSocket ∧
              UnaryHistory handoffRead ∧ UnaryHistory socketRead ∧
                Cont handoff obstruction dischargeSocket ∧
                  Cont handoff obstruction socketRead ∧
                    Cont handoff localName handoffRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro packet socketRoute handoffReadRoute handoffReadPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed handoffUnary localNameUnary handoffReadRoute
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary socketRoute
  exact
    ⟨handoffUnary, obstructionUnary, dischargeSocketUnary, handoffReadUnary,
      socketReadUnary, handoffObstructionSocket, socketRoute, handoffReadRoute,
      provenancePkg, handoffReadPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
