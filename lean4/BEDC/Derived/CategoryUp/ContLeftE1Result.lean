import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist BEDC.FKernel.Cont

theorem category_cont_left_e1_result_cases {h k r : BHist} :
    Cont (BHist.e1 h) k (BHist.e1 r) ->
      (k = BHist.Empty ∧ hsame h r) ∨
        (∃ k1 : BHist, k = BHist.e1 k1 ∧ Cont (BHist.e1 h) k1 r) := by
  intro hcont
  cases k with
  | Empty =>
      left
      constructor
      · rfl
      · exact (BHist.e1.inj hcont).symm
  | e0 k0 =>
      cases hcont
  | e1 k1 =>
      right
      exact Exists.intro k1 (And.intro rfl (BHist.e1.inj hcont))

end BEDC.Derived.CategoryUp
