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

theorem MetaCICCriticalPathResidualPublicHandoff [AskSetup] [PackageSetup]
    {candidate sn residual frontier socket l10 replay provenance localName handoff
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont candidate sn frontier →
      Cont frontier residual handoff →
        Cont handoff socket replay →
          Cont replay localName publicRead →
            PkgSig bundle provenance pkg →
              PkgSig bundle publicRead pkg →
                UnaryHistory candidate →
                  UnaryHistory sn →
                    UnaryHistory residual →
                      UnaryHistory socket →
                        UnaryHistory localName →
                          SemanticNameCert
                              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row candidate ∨ hsame row sn ∨ hsame row residual ∨
                                  hsame row frontier ∨ hsame row socket ∨ hsame row l10 ∨
                                    hsame row handoff ∨ hsame row publicRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont candidate sn frontier ∧
                                  Cont frontier residual handoff ∧
                                    Cont handoff socket replay ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle publicRead pkg)
                              hsame ∧
                            UnaryHistory frontier ∧ UnaryHistory handoff ∧
                              UnaryHistory replay ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro candidateSnFrontier frontierResidualHandoff handoffSocketReplay replayLocalPublic
    provenancePkg publicPkg candidateUnary snUnary residualUnary socketUnary localNameUnary
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed candidateUnary snUnary candidateSnFrontier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed frontierUnary residualUnary frontierResidualHandoff
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed handoffUnary socketUnary handoffSocketReplay
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed replayUnary localNameUnary replayLocalPublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidate ∨ hsame row sn ∨ hsame row residual ∨ hsame row frontier ∨
              hsame row socket ∨ hsame row l10 ∨ hsame row handoff ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont candidate sn frontier ∧
              Cont frontier residual handoff ∧ Cont handoff socket replay ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        ⟨source.right, candidateSnFrontier, frontierResidualHandoff, handoffSocketReplay,
          provenancePkg, publicPkg⟩
  }
  exact ⟨cert, frontierUnary, handoffUnary, replayUnary, publicUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
