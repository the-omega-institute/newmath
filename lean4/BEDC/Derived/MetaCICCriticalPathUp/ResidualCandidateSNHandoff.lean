import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualCandidateSNHandoff [AskSetup] [PackageSetup]
    {candidate sn _normal residual frontier ledger socket l10 replay provenance localName
      handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont candidate sn frontier →
      Cont frontier residual handoff →
        Cont handoff socket replay →
          PkgSig bundle provenance pkg →
            PkgSig bundle localName pkg →
              UnaryHistory candidate →
                UnaryHistory sn →
                  UnaryHistory residual →
                    UnaryHistory socket →
                      SemanticNameCert
                          (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row candidate ∨ hsame row sn ∨ hsame row residual ∨
                              hsame row frontier ∨ hsame row ledger ∨ hsame row socket ∨
                                hsame row l10 ∨ hsame row handoff)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont candidate sn frontier ∧
                              Cont frontier residual handoff ∧ Cont handoff socket replay ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                          hsame ∧
                        UnaryHistory frontier ∧ UnaryHistory handoff ∧ UnaryHistory replay := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro candidateSNFrontier frontierResidualHandoff handoffSocketReplay provenancePkg
    localNamePkg candidateUnary snUnary residualUnary socketUnary
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed candidateUnary snUnary candidateSNFrontier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed frontierUnary residualUnary frontierResidualHandoff
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed handoffUnary socketUnary handoffSocketReplay
  have sourceHandoff :
      (fun row : BHist => hsame row handoff ∧ UnaryHistory row) handoff := by
    exact ⟨hsame_refl handoff, handoffUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidate ∨ hsame row sn ∨ hsame row residual ∨
              hsame row frontier ∨ hsame row ledger ∨ hsame row socket ∨
                hsame row l10 ∨ hsame row handoff)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont candidate sn frontier ∧
              Cont frontier residual handoff ∧ Cont handoff socket replay ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoff sourceHandoff
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, candidateSNFrontier, frontierResidualHandoff, handoffSocketReplay,
          provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, frontierUnary, handoffUnary, replayUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
