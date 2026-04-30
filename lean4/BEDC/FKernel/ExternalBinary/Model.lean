import BEDC.FKernel.ExternalBinary

namespace BEDC.FKernel.ExternalBinary

open BEDC.FKernel.Hist

theorem Mbin_cases (w : Mbin) :
    w = BHist.Empty ∨ (∃ t : Mbin, w = BHist.e0 t) ∨
      (∃ t : Mbin, w = BHist.e1 t) := by
  cases w with
  | Empty =>
      exact Or.inl rfl
  | e0 t =>
      exact Or.inr (Or.inl (Exists.intro t rfl))
  | e1 t =>
      exact Or.inr (Or.inr (Exists.intro t rfl))

end BEDC.FKernel.ExternalBinary
