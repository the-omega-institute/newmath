import BEDC.Derived.RegularCauchyTelescopingBudgetUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyTelescopingBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem RegularCauchyTelescopingBudgetWindowConcatenationRoute
    {W0 W1 D0 D1 S0 E1 combinedWindow combinedLedger : BHist} :
    UnaryHistory W0 ->
      UnaryHistory W1 ->
        UnaryHistory D0 ->
          UnaryHistory D1 ->
            Cont W0 W1 combinedWindow ->
              Cont D0 D1 combinedLedger ->
                hsame S0 E1 ->
                  SemanticNameCert
                      (fun row : BHist => hsame row combinedWindow ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row W0 ∨ hsame row W1 ∨ hsame row D0 ∨ hsame row D1 ∨
                          hsame row S0 ∨ hsame row E1 ∨ hsame row combinedWindow ∨
                            hsame row combinedLedger)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont W0 W1 combinedWindow ∧
                          Cont D0 D1 combinedLedger ∧ hsame S0 E1)
                      hsame ∧
                    UnaryHistory combinedWindow ∧ UnaryHistory combinedLedger ∧
                      hsame combinedWindow (append W0 W1) ∧
                        hsame combinedLedger (append D0 D1) := by
  -- BEDC touchpoint anchor: BHist Cont append hsame SemanticNameCert UnaryHistory
  intro w0Unary w1Unary d0Unary d1Unary windowRoute ledgerRoute boundarySame
  have combinedWindowUnary : UnaryHistory combinedWindow :=
    unary_cont_closed w0Unary w1Unary windowRoute
  have combinedLedgerUnary : UnaryHistory combinedLedger :=
    unary_cont_closed d0Unary d1Unary ledgerRoute
  have windowSameAppend : hsame combinedWindow (append W0 W1) := windowRoute
  have ledgerSameAppend : hsame combinedLedger (append D0 D1) := ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row combinedWindow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W0 ∨ hsame row W1 ∨ hsame row D0 ∨ hsame row D1 ∨
              hsame row S0 ∨ hsame row E1 ∨ hsame row combinedWindow ∨
                hsame row combinedLedger)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W0 W1 combinedWindow ∧
              Cont D0 D1 combinedLedger ∧ hsame S0 E1)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro combinedWindow ⟨hsame_refl combinedWindow, combinedWindowUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, windowRoute, ledgerRoute, boundarySame⟩
  }
  exact
    ⟨cert, combinedWindowUnary, combinedLedgerUnary, windowSameAppend, ledgerSameAppend⟩

end BEDC.Derived.RegularCauchyTelescopingBudgetUp
