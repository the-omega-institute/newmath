import BEDC.Derived.ModuleUp

namespace BEDC.Derived.ModuleUp

open BEDC.FKernel.Hist

theorem ModuleParitySmul_epsilon_double_action_empty_iff {m : BHist} :
    hsame (ModuleParitySmul ModuleParityEps (ModuleParitySmul ModuleParityEps m))
        BHist.Empty ↔
      hsame m BHist.Empty := by
  constructor
  · intro doubleEmpty
    cases m with
    | Empty =>
        exact hsame_refl BHist.Empty
    | e0 h =>
        exact False.elim (not_hsame_e1_empty doubleEmpty)
    | e1 h =>
        exact False.elim (not_hsame_e1_empty doubleEmpty)
  · intro mEmpty
    cases mEmpty
    exact hsame_refl BHist.Empty

theorem ModuleParitySmul_epsilon_double_action_one_iff {m : BHist} :
    hsame (ModuleParitySmul ModuleParityEps (ModuleParitySmul ModuleParityEps m))
        ModuleParityOne ↔
      (hsame m BHist.Empty -> False) := by
  cases m with
  | Empty =>
      exact Iff.intro
        (fun sameResult => False.elim (not_hsame_emp_e1 sameResult))
        (fun nonempty => False.elim (nonempty (hsame_refl BHist.Empty)))
  | e0 h =>
      exact Iff.intro
        (fun _sameResult sameInput => not_hsame_e0_empty sameInput)
        (fun _nonempty => hsame_refl ModuleParityOne)
  | e1 h =>
      exact Iff.intro
        (fun _sameResult sameInput => not_hsame_e1_empty sameInput)
        (fun _nonempty => hsame_refl ModuleParityOne)

theorem ModuleSingletonAssociativityBoundaryAdditiveUnitActionLaws :
    ModuleSingletonCarrier BHist.Empty ∧
      ModuleSingletonClassifier (ModuleSingletonSmul ModuleSingletonOne BHist.Empty)
        BHist.Empty ∧
        hsame (ModuleSingletonSmul (BHist.e1 BHist.Empty) BHist.Empty)
          (ModuleSingletonSmul BHist.Empty BHist.Empty) ∧
          (ModuleSingletonClassifier (BHist.e1 BHist.Empty) BHist.Empty -> False) := by
  -- BEDC touchpoint anchor: BHist hsame ModuleSingletonCarrier ModuleSingletonClassifier
  have emptyCarrier : ModuleSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have unitClassified :
      ModuleSingletonClassifier (ModuleSingletonSmul ModuleSingletonOne BHist.Empty)
        BHist.Empty :=
    Iff.mpr ModuleSingletonClassifier_empty_endpoints_iff
      ⟨hsame_refl BHist.Empty, hsame_refl BHist.Empty⟩
  have visibleScalarSame :
      hsame (ModuleSingletonSmul (BHist.e1 BHist.Empty) BHist.Empty)
        (ModuleSingletonSmul BHist.Empty BHist.Empty) :=
    hsame_refl BHist.Empty
  have visibleScalarBoundary :
      ModuleSingletonClassifier (BHist.e1 BHist.Empty) BHist.Empty -> False := by
    intro classified
    exact not_hsame_e1_empty classified.left
  exact ⟨emptyCarrier, unitClassified, visibleScalarSame, visibleScalarBoundary⟩

end BEDC.Derived.ModuleUp
