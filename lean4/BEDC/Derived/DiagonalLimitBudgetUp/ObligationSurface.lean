import BEDC.Derived.DiagonalLimitBudgetUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DiagonalLimitBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DiagonalLimitBudgetObligationSurface (x : DiagonalLimitBudgetUp) :
    ∃ D M W Q E H C P N : BHist,
      x = DiagonalLimitBudgetUp.mk D M W Q E H C P N ∧
        Cont D M (append D M) ∧
          Cont W Q (append W Q) ∧
            Cont Q E (append Q E) ∧
              Cont (append D M) (append W Q) (append (append D M) (append W Q)) ∧
                SemanticNameCert
                  (fun row : BHist =>
                    hsame row D ∨ hsame row M ∨ hsame row W ∨ hsame row Q ∨ hsame row E)
                  (fun row : BHist =>
                    hsame row D ∨ hsame row M ∨ hsame row W ∨ hsame row Q ∨
                      hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N)
                  (fun row : BHist =>
                    (hsame row D ∨ hsame row M ∨ hsame row W ∨ hsame row Q ∨
                      hsame row E) ∧
                      Cont D M (append D M) ∧
                        Cont W Q (append W Q) ∧ Cont Q E (append Q E))
                  hsame ∧
              SemanticNameCert
                (fun row : BHist => hsame row E)
                (fun row : BHist =>
                  hsame row D ∨ hsame row M ∨ hsame row W ∨ hsame row Q ∨
                    hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N)
                (fun row : BHist =>
                  hsame row E ∧ Cont D M (append D M) ∧ Cont W Q (append W Q))
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert
  cases x with
  | mk D M W Q E H C P N =>
      exact
        ⟨D, M, W, Q, E, H, C, P, N, rfl, cont_intro rfl, cont_intro rfl,
          cont_intro rfl, cont_intro rfl,
          {
            core := {
              carrier_inhabited := Exists.intro D (Or.inl (hsame_refl D))
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
                intro _row _other sameRows sourceRow
                cases sameRows
                exact sourceRow
            }
            pattern_sound := by
              intro _row sourceRow
              cases sourceRow with
              | inl sameD =>
                  exact Or.inl sameD
              | inr sourceTail =>
                  cases sourceTail with
                  | inl sameM =>
                      exact Or.inr (Or.inl sameM)
                  | inr sourceTail =>
                      cases sourceTail with
                      | inl sameW =>
                          exact Or.inr (Or.inr (Or.inl sameW))
                      | inr sourceTail =>
                          cases sourceTail with
                          | inl sameQ =>
                              exact Or.inr (Or.inr (Or.inr (Or.inl sameQ)))
                          | inr sameE =>
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameE))))
            ledger_sound := by
              intro _row sourceRow
              exact
                ⟨sourceRow, cont_intro rfl, cont_intro rfl, cont_intro rfl⟩
          },
          {
            core := {
              carrier_inhabited := Exists.intro E (hsame_refl E)
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
                intro _row _other sameRows sourceRow
                exact hsame_trans (hsame_symm sameRows) sourceRow
            }
            pattern_sound := by
              intro _row sourceRow
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inl sourceRow))))
            ledger_sound := by
              intro _row sourceRow
              exact ⟨sourceRow, cont_intro rfl, cont_intro rfl⟩
          }⟩

end BEDC.Derived.DiagonalLimitBudgetUp
