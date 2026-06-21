import BEDC.Derived.WritingItemAuditUp.TasteGate
import BEDC.FKernel.Unary

namespace BEDC.Derived.WritingItemAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem WritingItemAudit_public_status [AskSetup] [PackageSetup]
    {K C R L T F G Q H U P N registryRead exportRead publicStatus : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory exportRead →
      UnaryHistory N →
        Cont T F registryRead →
          Cont registryRead Q exportRead →
            Cont exportRead N publicStatus →
              PkgSig bundle publicStatus pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row publicStatus ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row T ∨ hsame row F ∨ hsame row G ∨ hsame row Q ∨
                        hsame row exportRead ∨ hsame row publicStatus)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont T F registryRead ∧
                        Cont registryRead Q exportRead ∧
                          Cont exportRead N publicStatus ∧
                            PkgSig bundle publicStatus pkg)
                    hsame ∧
                  writingItemAuditFields
                      (WritingItemAuditUp.mk K C R L T F G Q H U P N) =
                    [K, C, R, L, T, F, G, Q, H, U, P, N] ∧
                    Nonempty (ChapterTasteGate WritingItemAuditUp) ∧
                      Nonempty (FieldFaithful WritingItemAuditUp) ∧
                        Nonempty (Nontrivial WritingItemAuditUp) := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro exportUnary nameUnary registryRoute exportRoute statusRoute statusPkg
  have publicUnary : UnaryHistory publicStatus :=
    unary_cont_closed exportUnary nameUnary statusRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicStatus ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row F ∨ hsame row G ∨ hsame row Q ∨
              hsame row exportRead ∨ hsame row publicStatus)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T F registryRead ∧ Cont registryRead Q exportRead ∧
              Cont exportRead N publicStatus ∧ PkgSig bundle publicStatus pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicStatus ⟨hsame_refl publicStatus, publicUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, registryRoute, exportRoute, statusRoute, statusPkg⟩
  }
  exact
    ⟨cert, rfl, ⟨writingItemAuditChapterTasteGate⟩, ⟨writingItemAuditFieldFaithful⟩,
      ⟨writingItemAuditNontrivial⟩⟩

end BEDC.Derived.WritingItemAuditUp
