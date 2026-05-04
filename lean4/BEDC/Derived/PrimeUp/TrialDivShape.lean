import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TrialDiv_bound_unit_or_successor_shape {b n : BHist} :
    TrialDiv b n ->
      hsame b (BHist.e1 BHist.Empty) ∨
        (∃ t : BHist, hsame b (BHist.e1 (BHist.e1 t)) ∧ UnaryHistory t) := by
  intro trial
  have shape := TrialDiv_bound_positive_shape trial
  cases shape with
  | intro tail data =>
      cases tail with
      | Empty =>
          exact Or.inl data.left
      | e0 tail =>
          exact False.elim (unary_no_zero_extension data.right)
      | e1 tail =>
          exact Or.inr
            (Exists.intro tail (And.intro data.left (unary_e1_inversion data.right)))

end BEDC.Derived.PrimeUp
