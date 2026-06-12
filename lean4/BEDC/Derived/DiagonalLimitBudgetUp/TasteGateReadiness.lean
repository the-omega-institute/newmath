import BEDC.Derived.DiagonalLimitBudgetUp.TasteGate

namespace BEDC.Derived.DiagonalLimitBudgetUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

private theorem diagonalLimitBudget_empty_e0_packets_distinct :
    DiagonalLimitBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty ≠
      DiagonalLimitBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  injection h with hrequest _ _ _ _ _ _ _ _
  exact not_hsame_emp_e0 hrequest

theorem DiagonalLimitBudgetTasteGateReadiness :
    Nonempty (Nontrivial DiagonalLimitBudgetUp) ∧
      Nonempty (FieldFaithful DiagonalLimitBudgetUp) ∧
        ∃ x y : DiagonalLimitBudgetUp,
          x =
              DiagonalLimitBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
            y =
                DiagonalLimitBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
              x ≠ y ∧
                BHistCarrier.toEventFlow x ≠ BHistCarrier.toEventFlow y ∧
                  FieldFaithful.fields x ≠ FieldFaithful.fields y := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨diagonalLimitBudgetNontrivial⟩
  · constructor
    · exact ⟨diagonalLimitBudgetFieldFaithful⟩
    · let x :=
        DiagonalLimitBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      let y :=
        DiagonalLimitBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      refine ⟨x, y, rfl, rfl, ?_, ?_, ?_⟩
      · intro h
        exact diagonalLimitBudget_empty_e0_packets_distinct h
      · intro h
        exact
          (ChapterTasteGate.layer_separation x y
            diagonalLimitBudget_empty_e0_packets_distinct) h
      · intro h
        have hxy : x = y := FieldFaithful.field_faithful x y h
        exact diagonalLimitBudget_empty_e0_packets_distinct hxy

end BEDC.Derived.DiagonalLimitBudgetUp
