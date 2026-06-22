import BEDC.Derived.FableBranchWitnessUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FableBranchWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem FableBranchWitnessCarrier_empty_boundary_selector_dependency
    {h m r E A H C P N selectorRead dependencyRead : BHist} :
    UnaryHistory h ->
      UnaryHistory E ->
        UnaryHistory C ->
          UnaryHistory N ->
            Cont h E r ->
              Cont C N dependencyRead ->
                SemanticNameCert
                    (fun row : BHist => hsame row dependencyRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row h ∨ hsame row m ∨ hsame row r ∨ hsame row E ∨
                        hsame row A ∨ hsame row C ∨ hsame row N ∨
                          hsame row dependencyRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont h E r ∧ Cont C N dependencyRead ∧
                        fableBranchWitnessEncodeBHist BHist.Empty = ([] : List BMark))
                    hsame ∧
                  UnaryHistory r ∧ UnaryHistory dependencyRead := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame SemanticNameCert UnaryHistory
  intro hUnary EUnary CUnary NUnary emptyRoute dependencyRoute
  have rUnary : UnaryHistory r :=
    unary_cont_closed hUnary EUnary emptyRoute
  have dependencyReadUnary : UnaryHistory dependencyRead :=
    unary_cont_closed CUnary NUnary dependencyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dependencyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row h ∨ hsame row m ∨ hsame row r ∨ hsame row E ∨
              hsame row A ∨ hsame row C ∨ hsame row N ∨ hsame row dependencyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont h E r ∧ Cont C N dependencyRead ∧
              fableBranchWitnessEncodeBHist BHist.Empty = ([] : List BMark))
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro dependencyRead
          ⟨hsame_refl dependencyRead, dependencyReadUnary⟩
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr sourceRow.left))))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, emptyRoute, dependencyRoute, rfl⟩
    }
  exact ⟨cert, rUnary, dependencyReadUnary⟩

end BEDC.Derived.FableBranchWitnessUp
