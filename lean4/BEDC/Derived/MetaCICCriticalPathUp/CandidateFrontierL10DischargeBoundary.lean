import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateFrontierL10DischargeBoundary [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateRead l10Read socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route dischargeSocket candidateRead →
        Cont candidateRead localName l10Read →
          Cont candidateRead obstruction socketRead →
            PkgSig bundle l10Read pkg →
              PkgSig bundle socketRead pkg →
                UnaryHistory candidateRead ∧ UnaryHistory l10Read ∧
                  UnaryHistory socketRead ∧ Cont route dischargeSocket candidateRead ∧
                    Cont candidateRead localName l10Read ∧
                      Cont candidateRead obstruction socketRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle l10Read pkg ∧
                          PkgSig bundle socketRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro packet routeDischargeCandidate candidateLocalNameL10 candidateObstructionSocket
    l10Pkg socketPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed routeUnary dischargeSocketUnary routeDischargeCandidate
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed candidateUnary localNameUnary candidateLocalNameL10
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed candidateUnary obstructionUnary candidateObstructionSocket
  exact
    ⟨candidateUnary, l10Unary, socketUnary, routeDischargeCandidate,
      candidateLocalNameL10, candidateObstructionSocket, provenancePkg, l10Pkg, socketPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
