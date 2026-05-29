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

theorem MetaCICCriticalPathCandidateSNBoundary [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateRead dischargeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont strongNorm normalForm route ->
        Cont route handoff candidateRead ->
          Cont candidateRead dischargeSocket dischargeRead ->
            PkgSig bundle dischargeRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row candidateRead ∨ hsame row dischargeSocket ∨
                      hsame row dischargeRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row candidateRead ∨ hsame row dischargeSocket ∨
                      hsame row dischargeRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧
                      (hsame row candidateRead ∨ hsame row dischargeSocket ∨
                        hsame row dischargeRead) ∧
                      PkgSig bundle dischargeRead pkg)
                  hsame ∧
                UnaryHistory candidateRead ∧ UnaryHistory dischargeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro packet _strongNormNormalFormRoute routeHandoffCandidate candidateSocketDischarge
    dischargePkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, _localNameUnary,
    _packetStrongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed routeUnary handoffUnary routeHandoffCandidate
  have dischargeUnary : UnaryHistory dischargeRead :=
    unary_cont_closed candidateUnary dischargeSocketUnary candidateSocketDischarge
  have sourceDischarge :
      (fun row : BHist =>
        (hsame row candidateRead ∨ hsame row dischargeSocket ∨ hsame row dischargeRead) ∧
          UnaryHistory row) dischargeRead := by
    exact ⟨Or.inr (Or.inr (hsame_refl dischargeRead)), dischargeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row candidateRead ∨ hsame row dischargeSocket ∨
              hsame row dischargeRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row dischargeSocket ∨ hsame row dischargeRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              (hsame row candidateRead ∨ hsame row dischargeSocket ∨
                hsame row dischargeRead) ∧
              PkgSig bundle dischargeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dischargeRead sourceDischarge
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        constructor
        · cases source.left with
          | inl sameCandidate =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameCandidate)
          | inr rest =>
              cases rest with
              | inl sameSocket =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameSocket))
              | inr sameDischarge =>
                  exact
                    Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameDischarge))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, source.left, dischargePkg⟩
  }
  exact ⟨cert, candidateUnary, dischargeUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
