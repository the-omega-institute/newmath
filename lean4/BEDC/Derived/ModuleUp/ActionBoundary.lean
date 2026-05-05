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

end BEDC.Derived.ModuleUp
