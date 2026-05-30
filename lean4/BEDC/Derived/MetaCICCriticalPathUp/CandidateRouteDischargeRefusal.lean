import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateRouteDischargeRefusal [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route dischargeSocket candidateRead →
        Cont candidateRead obstruction socketRead →
          PkgSig bundle socketRead pkg →
            UnaryHistory route ∧ UnaryHistory dischargeSocket ∧ UnaryHistory candidateRead ∧
              UnaryHistory obstruction ∧ UnaryHistory socketRead ∧
                Cont route dischargeSocket candidateRead ∧
                  Cont candidateRead obstruction socketRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle socketRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro packet routeDischargeCandidate candidateObstructionSocket socketPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed routeUnary dischargeSocketUnary routeDischargeCandidate
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed candidateUnary obstructionUnary candidateObstructionSocket
  exact
    ⟨routeUnary, dischargeSocketUnary, candidateUnary, obstructionUnary, socketUnary,
      routeDischargeCandidate, candidateObstructionSocket, provenancePkg, socketPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
