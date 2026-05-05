import BEDC.Derived.DirichletSeriesUp

namespace BEDC.Derived.DirichletSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem DirichletCoefficient_completely_multiplicative_product_nonempty
    {coeff : BHist -> BHist} {m n : BHist} :
    DirichletCoefficient_completely_multiplicative coeff ->
      DirichletPositiveIndex m -> DirichletPositiveIndex n ->
        (hsame (coeff m) BHist.Empty -> False) ->
          (hsame (coeff n) BHist.Empty -> False) ->
            hsame (coeff (append m n)) BHist.Empty -> False := by
  intro multiplicative positiveM positiveN coeffMNonempty coeffNNonempty productEmpty
  have productShape :
      hsame (coeff (append m n)) (append (coeff m) (coeff n)) :=
    multiplicative.right positiveM positiveN
  have factorsEmpty :
      hsame (coeff m) BHist.Empty ∧ hsame (coeff n) BHist.Empty :=
    append_eq_empty_iff.mp (hsame_trans (hsame_symm productShape) productEmpty)
  exact coeffMNonempty factorsEmpty.left

end BEDC.Derived.DirichletSeriesUp
