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

theorem MetaCICCriticalPathCandidateDischargeFrontier [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont route dischargeSocket candidateRead ->
        Cont candidateRead obstruction socketRead ->
          PkgSig bundle candidateRead pkg ->
            PkgSig bundle socketRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row candidateRead ∨ hsame row socketRead)
                  (fun row : BHist =>
                    hsame row obstruction ∨ hsame row dischargeSocket ∨
                      hsame row candidateRead ∨ hsame row socketRead)
                  (fun row : BHist =>
                    PkgSig bundle row pkg ∧
                      (hsame row candidateRead ∨ hsame row socketRead))
                  hsame ∧
                UnaryHistory candidateRead ∧ UnaryHistory socketRead ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeSocketCandidate candidateObstructionSocket candidatePkg socketPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed routeUnary dischargeSocketUnary routeSocketCandidate
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed candidateUnary obstructionUnary candidateObstructionSocket
  have sourceCandidate :
      (fun row : BHist => hsame row candidateRead ∨ hsame row socketRead) candidateRead := by
    exact Or.inl (hsame_refl candidateRead)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row candidateRead ∨ hsame row socketRead)
          (fun row : BHist =>
            hsame row obstruction ∨ hsame row dischargeSocket ∨
              hsame row candidateRead ∨ hsame row socketRead)
          (fun row : BHist =>
            PkgSig bundle row pkg ∧ (hsame row candidateRead ∨ hsame row socketRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro candidateRead sourceCandidate
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
        cases source with
        | inl sameCandidate =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameCandidate)
        | inr sameSocket =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameSocket)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameCandidate =>
          exact Or.inr (Or.inr (Or.inl sameCandidate))
      | inr sameSocket =>
          exact Or.inr (Or.inr (Or.inr sameSocket))
    ledger_sound := by
      intro _row source
      cases source with
      | inl sameCandidate =>
          cases sameCandidate
          exact ⟨candidatePkg, Or.inl (hsame_refl candidateRead)⟩
      | inr sameSocket =>
          cases sameSocket
          exact ⟨socketPkg, Or.inr (hsame_refl socketRead)⟩
  }
  exact ⟨cert, candidateUnary, socketUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
