import BEDC.Derived.DiagonalLimitBudgetUp.TasteGate

namespace BEDC.Derived.DiagonalLimitBudgetUp

open BEDC.FKernel.Hist

theorem DiagonalLimitBudgetIndependenceWitness :
    ∃ x y : DiagonalLimitBudgetUp,
      x ≠ y ∧
        (∃ request window dyadic sealRow transport continuation provenance name : BHist,
          x =
              DiagonalLimitBudgetUp.mk request BHist.Empty window dyadic sealRow transport
                continuation provenance name ∧
            y =
              DiagonalLimitBudgetUp.mk request (BHist.e0 BHist.Empty) window dyadic sealRow
                transport continuation provenance name) := by
  -- BEDC touchpoint anchor: BHist Empty e0 DiagonalLimitBudgetUp
  let x :=
    DiagonalLimitBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  let y :=
    DiagonalLimitBudgetUp.mk BHist.Empty (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  refine ⟨x, y, ?_, ?_⟩
  · intro h
    injection h with _ hBudget
    cases hBudget
  · exact
      ⟨BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
        BHist.Empty, BHist.Empty, rfl, rfl⟩

end BEDC.Derived.DiagonalLimitBudgetUp
