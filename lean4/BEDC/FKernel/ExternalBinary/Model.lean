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

theorem Mbin_induction {P : Mbin → Prop} (empty : P BHist.Empty)
    (zero : ∀ w : Mbin, P w → P (BHist.e0 w))
    (one : ∀ w : Mbin, P w → P (BHist.e1 w)) : ∀ w : Mbin, P w := by
  intro w
  induction w with
  | Empty =>
      exact empty
  | e0 w ih =>
      exact zero w ih
  | e1 w ih =>
      exact one w ih

end BEDC.FKernel.ExternalBinary
