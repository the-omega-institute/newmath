import BEDC.Derived.MetricUp.SOneEquationDistanceFactorization

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ProdUp
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp
open BEDC.Derived.S1Up

theorem MetricspaceRealalgorderSonePositiveBoundaryEquivalence
    {x y equation point dist radius witness budget classifier provenance realAlg positiveRead :
      BHist} :
    SOneHistoryCarrier x y equation point ->
      MetricspaceRealDistanceCarrier x y dist radius witness budget classifier provenance realAlg ->
        Cont radius realAlg positiveRead ->
          MetricDistanceWitness x y dist ∧ UnaryHistory positiveRead ∧
            Cont radius realAlg positiveRead ∧ hsame classifier dist ∧ UnaryHistory point ∧
              Cont x y point ∧ hsame equation SOneUnitHistory := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory MetricDistanceWitness
  intro sone metric positiveRoute
  have metricRows :=
    MetricspaceRealalgorderPositiveDistancePublicCorrespondence metric positiveRoute
  have soneRows := SOneHistoryCarrier_public_readback sone
  have realConstantUnary : ∀ {row : BHist}, RealConstantHistoryCarrier row -> UnaryHistory row := by
    intro row rowCarrier
    cases rowCarrier with
    | intro denominator data =>
        have denominatorUnary : UnaryHistory denominator :=
          (PositiveUnaryDenominator_unary_and_nonempty
            (RatHistoryCarrier_iff_positive_denominator.mp data.right)).left
        exact unary_transport (unary_e1_closed denominatorUnary) (hsame_symm data.left)
  have pointUnary : UnaryHistory point :=
    ProdHistoryCarrier_unary_of_components realConstantUnary realConstantUnary soneRows.left
  exact
    ⟨metricRows.left, metricRows.right.right.right.right.right.left,
      metricRows.right.right.right.right.right.right.left,
      metricRows.right.right.right.right.right.right.right.right, pointUnary,
      sone.right.right.right, soneRows.right.left⟩

end BEDC.Derived.MetricUp
