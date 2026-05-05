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

end BEDC.Derived.ModuleUp
