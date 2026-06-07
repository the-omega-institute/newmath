import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateFrontierSourceLockCertificate [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName sourceRead candidateRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName sourceRead →
        Cont sourceRead normalForm candidateRead →
          Cont candidateRead handoff handoffRead →
            PkgSig bundle handoffRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row sourceRead ∨ hsame row candidateRead ∨ hsame row handoff ∨
                      hsame row handoffRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle handoffRead pkg ∧
                      Cont candidateRead handoff handoffRead)
                  hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory candidateRead ∧
                  UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameSource sourceNormalCandidate candidateHandoffRead handoffReadPkg
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameSource
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed sourceUnary normalFormUnary sourceNormalCandidate
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffRead
  have sourceHandoffRead :
      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row) handoffRead := by
    exact ⟨hsame_refl handoffRead, handoffReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceRead ∨ hsame row candidateRead ∨ hsame row handoff ∨
              hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle handoffRead pkg ∧
              Cont candidateRead handoff handoffRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead sourceHandoffRead
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, handoffReadPkg, candidateHandoffRead⟩
  }
  exact ⟨cert, sourceUnary, candidateUnary, handoffReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
