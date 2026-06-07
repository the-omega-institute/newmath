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

theorem MetaCICCriticalPathCandidateMediatedNormalizationBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateBudget frontierBudget socketBudget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route handoff candidateBudget →
        Cont candidateBudget normalForm frontierBudget →
          Cont frontierBudget obstruction socketBudget →
            PkgSig bundle socketBudget pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row candidateBudget ∨ hsame row frontierBudget ∨
                        hsame row socketBudget) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                      hsame row handoff ∨ hsame row dischargeSocket ∨
                        hsame row candidateBudget ∨ hsame row frontierBudget ∨
                          hsame row socketBudget)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle socketBudget pkg ∧
                      PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory candidateBudget ∧ UnaryHistory frontierBudget ∧
                  UnaryHistory socketBudget := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeHandoffCandidate candidateNormalFrontier frontierObstructionSocket
    socketBudgetPkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateBudget :=
    unary_cont_closed routeUnary handoffUnary routeHandoffCandidate
  have frontierUnary : UnaryHistory frontierBudget :=
    unary_cont_closed candidateUnary normalFormUnary candidateNormalFrontier
  have socketUnary : UnaryHistory socketBudget :=
    unary_cont_closed frontierUnary obstructionUnary frontierObstructionSocket
  have sourceSocket :
      (fun row : BHist =>
        (hsame row candidateBudget ∨ hsame row frontierBudget ∨ hsame row socketBudget) ∧
          UnaryHistory row) socketBudget := by
    exact ⟨Or.inr (Or.inr (hsame_refl socketBudget)), socketUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row candidateBudget ∨ hsame row frontierBudget ∨
                hsame row socketBudget) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row candidateBudget ∨
                hsame row frontierBudget ∨ hsame row socketBudget)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle socketBudget pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketBudget sourceSocket
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
        have transportSame : ∀ {target : BHist}, hsame _row target → hsame _other target := by
          intro target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        have sourceDisj :
            hsame _other candidateBudget ∨ hsame _other frontierBudget ∨
              hsame _other socketBudget := by
          cases source.left with
          | inl sameCandidate =>
              exact Or.inl (transportSame sameCandidate)
          | inr rest =>
              cases rest with
              | inl sameFrontier =>
                  exact Or.inr (Or.inl (transportSame sameFrontier))
              | inr sameSocket =>
                  exact Or.inr (Or.inr (transportSame sameSocket))
        exact ⟨sourceDisj, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameCandidate =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameCandidate)))))
      | inr rest =>
          cases rest with
          | inl sameFrontier =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameFrontier))))))
          | inr sameSocket =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr sameSocket))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, socketBudgetPkg, provenancePkg⟩
  }
  exact ⟨cert, candidateUnary, frontierUnary, socketUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
