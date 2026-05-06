import BEDC.Derived.ComplexLimitUp

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist

theorem ComplexLimit_conditional_unique_boundary {s N M M' : BHist -> BHist}
    {z z' diagonal : BHist} :
    ComplexLimit s N z M -> ComplexLimit s N z' M' -> ComplexDistance z z' diagonal ->
      hsame diagonal BHist.Empty -> hsame z z' := by
  intro _limitZ _limitZ' distance diagonalEmpty
  have transportedDistance :
      ComplexDistance z z' BHist.Empty :=
    (ComplexDistance_hsame_transport_with_relation (hsame_refl z) (hsame_refl z')
      diagonalEmpty distance).left
  have endpoints := ComplexDistance_empty_iff.mp transportedDistance
  exact hsame_trans endpoints.right.right.left (hsame_symm endpoints.right.right.right)

end BEDC.Derived.ComplexLimitUp
