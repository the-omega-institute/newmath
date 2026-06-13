import BEDC.Derived.DiagonalLimitBudgetUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DiagonalLimitBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DiagonalLimitBudgetRealSealHandoff (x : DiagonalLimitBudgetUp) :
    ∃ D M W Q E H C P N requestBudget selectedWindow dyadicRead sealRead : BHist,
      x = DiagonalLimitBudgetUp.mk D M W Q E H C P N ∧
        Cont D M requestBudget ∧
          Cont requestBudget W selectedWindow ∧
            Cont selectedWindow Q dyadicRead ∧
              Cont dyadicRead E sealRead ∧
                hsame sealRead (append dyadicRead E) ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row sealRead)
                    (fun row : BHist =>
                      hsame row D ∨ hsame row M ∨ hsame row W ∨ hsame row Q ∨
                        hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                          hsame row N ∨ hsame row sealRead)
                    (fun row : BHist =>
                      hsame row sealRead ∧ Cont D M requestBudget ∧
                        Cont requestBudget W selectedWindow ∧
                          Cont selectedWindow Q dyadicRead ∧ Cont dyadicRead E sealRead)
                    hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert append
  cases x with
  | mk D M W Q E H C P N =>
      exact
        ⟨D, M, W, Q, E, H, C, P, N, append D M, append (append D M) W,
          append (append (append D M) W) Q, append (append (append (append D M) W) Q) E,
          rfl, cont_intro rfl, cont_intro rfl, cont_intro rfl, cont_intro rfl,
          hsame_refl (append (append (append (append D M) W) Q) E),
          {
            core := {
              carrier_inhabited :=
                Exists.intro (append (append (append (append D M) W) Q) E)
                  (hsame_refl (append (append (append (append D M) W) Q) E))
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
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr sourceRow))))))))
            ledger_sound := by
              intro _row sourceRow
              exact
                ⟨sourceRow, cont_intro rfl, cont_intro rfl, cont_intro rfl,
                  cont_intro rfl⟩
          }⟩

end BEDC.Derived.DiagonalLimitBudgetUp
