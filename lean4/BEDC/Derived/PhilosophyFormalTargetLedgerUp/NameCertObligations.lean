import BEDC.Derived.PhilosophyFormalTargetLedgerUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PhilosophyFormalTargetLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem PhilosophyFormalTargetLedger_namecert_obligations
    {registryRow theoremRow gapRow traditionRow scienceRow cannotClaimRow closureRow
      skeletonRow boundaryRow transportRow continuationRow provenanceRow nameCertRow
      auditRead : BHist} :
    Cont continuationRow provenanceRow auditRead →
      SemanticNameCert
          (fun row : BHist =>
            hsame row registryRow ∨ hsame row theoremRow ∨ hsame row gapRow ∨
              hsame row traditionRow ∨ hsame row scienceRow ∨
                hsame row cannotClaimRow ∨ hsame row closureRow ∨
                  hsame row skeletonRow ∨ hsame row boundaryRow ∨
                    hsame row transportRow ∨ hsame row continuationRow ∨
                      hsame row provenanceRow ∨ hsame row nameCertRow)
          (fun row : BHist =>
            (hsame row registryRow ∨ hsame row theoremRow ∨ hsame row gapRow ∨
              hsame row traditionRow ∨ hsame row scienceRow ∨
                hsame row cannotClaimRow ∨ hsame row closureRow ∨
                  hsame row skeletonRow ∨ hsame row boundaryRow ∨
                    hsame row transportRow ∨ hsame row continuationRow ∨
                      hsame row provenanceRow ∨ hsame row nameCertRow) ∨
              hsame row auditRead)
          (fun row : BHist =>
            (hsame row registryRow ∨ hsame row theoremRow ∨ hsame row gapRow ∨
              hsame row traditionRow ∨ hsame row scienceRow ∨
                hsame row cannotClaimRow ∨ hsame row closureRow ∨
                  hsame row skeletonRow ∨ hsame row boundaryRow ∨
                    hsame row transportRow ∨ hsame row continuationRow ∨
                      hsame row provenanceRow ∨ hsame row nameCertRow) ∧
              Cont continuationRow provenanceRow auditRead)
          hsame ∧
        Cont continuationRow provenanceRow auditRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert
  intro route
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row registryRow ∨ hsame row theoremRow ∨ hsame row gapRow ∨
              hsame row traditionRow ∨ hsame row scienceRow ∨
                hsame row cannotClaimRow ∨ hsame row closureRow ∨
                  hsame row skeletonRow ∨ hsame row boundaryRow ∨
                    hsame row transportRow ∨ hsame row continuationRow ∨
                      hsame row provenanceRow ∨ hsame row nameCertRow)
          (fun row : BHist =>
            (hsame row registryRow ∨ hsame row theoremRow ∨ hsame row gapRow ∨
              hsame row traditionRow ∨ hsame row scienceRow ∨
                hsame row cannotClaimRow ∨ hsame row closureRow ∨
                  hsame row skeletonRow ∨ hsame row boundaryRow ∨
                    hsame row transportRow ∨ hsame row continuationRow ∨
                      hsame row provenanceRow ∨ hsame row nameCertRow) ∨
              hsame row auditRead)
          (fun row : BHist =>
            (hsame row registryRow ∨ hsame row theoremRow ∨ hsame row gapRow ∨
              hsame row traditionRow ∨ hsame row scienceRow ∨
                hsame row cannotClaimRow ∨ hsame row closureRow ∨
                  hsame row skeletonRow ∨ hsame row boundaryRow ∨
                    hsame row transportRow ∨ hsame row continuationRow ∨
                      hsame row provenanceRow ∨ hsame row nameCertRow) ∧
              Cont continuationRow provenanceRow auditRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro registryRow (Or.inl (hsame_refl registryRow))
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inl source
    ledger_sound := by
      intro _row source
      exact ⟨source, route⟩
  }
  exact ⟨cert, route⟩

end BEDC.Derived.PhilosophyFormalTargetLedgerUp
