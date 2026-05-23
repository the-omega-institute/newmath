import BEDC.Derived.MetricUp
import BEDC.Derived.MetricUp.RealAlgOrderPositiveDistancePublicCorrespondence
import BEDC.Derived.S1Up

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.S1Up

theorem MetricspaceOpenPhaseConsumerInterface {p q x y d consumer : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p d) q) →
      Cont d consumer BHist.Empty →
        UnaryHistory p ∧ UnaryHistory q ∧ hsame x BHist.Empty ∧
          hsame y BHist.Empty ∧ hsame consumer BHist.Empty := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro visible consumerRoute
  have consumerBoundary := cont_empty_result_inversion consumerRoute
  cases consumerBoundary.left
  have emptyVisible :
      MetricDistanceWitness (append p x) (append y q)
        (append (append p BHist.Empty) q) := visible
  have context :=
    (MetricDistanceWitness_visible_context_empty_distance_iff (p := p) (q := q)
      (x := x) (y := y)).mp emptyVisible
  exact
    ⟨context.left, context.right.left, context.right.right.left,
      context.right.right.right, consumerBoundary.right⟩

theorem MetricspaceApartnessPositiveDistanceTriangleBoundary
    {p q x y z dxy dyz dxz : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) →
      MetricDistanceWitness (append p y) (append z q) (append (append p dyz) q) →
        MetricDistanceWitness (append p x) (append z q) (append (append p dxz) q) →
          UnaryHistory p ∧ UnaryHistory q ∧ UnaryHistory x ∧ UnaryHistory y ∧
            UnaryHistory z ∧ UnaryHistory dxy ∧ UnaryHistory dyz ∧ UnaryHistory dxz := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro xy yz xz
  have xyContext :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := dxy)).mp xy
  have yzContext :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := y) (y := z)
      (d := dyz)).mp yz
  have xzContext :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := z)
      (d := dxz)).mp xz
  exact
    ⟨xyContext.left, xyContext.right.left, xyContext.right.right.left,
      xyContext.right.right.right.left, yzContext.right.right.right.left,
      xyContext.right.right.right.right.left, yzContext.right.right.right.right.left,
      xzContext.right.right.right.right.left⟩

theorem MetricspaceRealalgorderTriangleConsumerExhaustion
    {p q x y z dxy dyz dxz radiusXY radiusYZ witnessXY witnessYZ budgetXY budgetYZ
      classifierXY classifierYZ provenanceXY provenanceYZ realAlgXY realAlgYZ positiveXY
      positiveYZ : BHist} :
    MetricspaceRealDistanceCarrier x y dxy radiusXY witnessXY budgetXY classifierXY
        provenanceXY realAlgXY ->
      MetricspaceRealDistanceCarrier y z dyz radiusYZ witnessYZ budgetYZ classifierYZ
          provenanceYZ realAlgYZ ->
        Cont radiusXY realAlgXY positiveXY ->
          Cont radiusYZ realAlgYZ positiveYZ ->
            MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) ->
              MetricDistanceWitness (append p y) (append z q) (append (append p dyz) q) ->
                MetricDistanceWitness (append p x) (append z q) (append (append p dxz) q) ->
                  UnaryHistory p ∧ UnaryHistory q ∧ UnaryHistory x ∧ UnaryHistory y ∧
                    UnaryHistory z ∧ UnaryHistory dxy ∧ UnaryHistory dyz ∧
                      UnaryHistory dxz ∧ UnaryHistory positiveXY ∧
                        UnaryHistory positiveYZ ∧ Cont radiusXY realAlgXY positiveXY ∧
                          Cont radiusYZ realAlgYZ positiveYZ ∧ hsame classifierXY dxy ∧
                            hsame classifierYZ dyz := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrierXY carrierYZ positiveXYRoute positiveYZRoute visibleXY visibleYZ visibleXZ
  have xyPublic :=
    MetricspaceRealalgorderPositiveDistancePublicCorrespondence carrierXY positiveXYRoute
  have yzPublic :=
    MetricspaceRealalgorderPositiveDistancePublicCorrespondence carrierYZ positiveYZRoute
  have triangleRows :=
    MetricspaceApartnessPositiveDistanceTriangleBoundary visibleXY visibleYZ visibleXZ
  exact
    ⟨triangleRows.left, triangleRows.right.left, triangleRows.right.right.left,
      triangleRows.right.right.right.left, triangleRows.right.right.right.right.left,
      triangleRows.right.right.right.right.right.left,
      triangleRows.right.right.right.right.right.right.left,
      triangleRows.right.right.right.right.right.right.right,
      xyPublic.right.right.right.right.right.left, yzPublic.right.right.right.right.right.left,
      xyPublic.right.right.right.right.right.right.left,
      yzPublic.right.right.right.right.right.right.left,
      xyPublic.right.right.right.right.right.right.right.right,
      yzPublic.right.right.right.right.right.right.right.right⟩

theorem MetricspaceSoneRealalgorderConsumerFactorization
    {x y equation point dist radius witness budget classifier provenance realAlg positiveRead :
      BHist} :
    SOneHistoryCarrier x y equation point ->
      MetricspaceRealDistanceCarrier x y dist radius witness budget classifier provenance realAlg ->
        Cont radius realAlg positiveRead ->
          MetricDistanceWitness x y dist ∧ UnaryHistory point ∧ Cont x y point ∧
            UnaryHistory positiveRead ∧ Cont radius realAlg positiveRead ∧ hsame classifier dist ∧
              Cont witness budget provenance := by
  -- BEDC touchpoint anchor: BHist Cont hsame MetricDistanceWitness
  intro sone carrier positiveRoute
  have soneRows := SOneHistoryCarrier_public_readback sone
  have metricRows := MetricspaceRealalgorderPositiveDistancePublicCorrespondence carrier positiveRoute
  have lawRows := MetricspaceRealDistanceCarrier_public_law_package carrier
  have realConstantUnary :
      ∀ {row : BHist}, BEDC.Derived.RealUp.RealConstantHistoryCarrier row -> UnaryHistory row := by
    intro row rowCarrier
    cases rowCarrier with
    | intro denominator data =>
        have denominatorUnary : UnaryHistory denominator :=
          (BEDC.Derived.RatUp.PositiveUnaryDenominator_unary_and_nonempty
            (BEDC.Derived.RatUp.RatHistoryCarrier_iff_positive_denominator.mp data.right)).left
        exact unary_transport (unary_e1_closed denominatorUnary) (hsame_symm data.left)
  have pointUnary : UnaryHistory point :=
    BEDC.Derived.ProdUp.ProdHistoryCarrier_unary_of_components realConstantUnary
      realConstantUnary soneRows.left
  exact
    ⟨metricRows.left, pointUnary, sone.right.right.right,
      metricRows.right.right.right.right.right.left,
      metricRows.right.right.right.right.right.right.left,
      metricRows.right.right.right.right.right.right.right.right,
      lawRows.right.right.right.right⟩

theorem MetricspaceRealalgorderSoneDistanceRouteExhaustion
    {x y equation point dist radius witness budget classifier provenance realAlg positiveRead :
      BHist} :
    SOneHistoryCarrier x y equation point ->
      MetricspaceRealDistanceCarrier x y dist radius witness budget classifier provenance realAlg ->
        Cont radius realAlg positiveRead ->
          MetricDistanceWitness x y dist ∧ UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory dist ∧
            UnaryHistory point ∧ UnaryHistory positiveRead ∧ Cont x y point ∧
              Cont radius realAlg positiveRead ∧ Cont witness budget provenance ∧
                hsame classifier dist := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory MetricDistanceWitness
  intro sone carrier positiveRoute
  have factored :=
    MetricspaceSoneRealalgorderConsumerFactorization sone carrier positiveRoute
  exact
    ⟨factored.left, factored.left.left, factored.left.right.left,
      factored.left.right.right.left, factored.right.left, factored.right.right.right.left,
      factored.right.right.left, factored.right.right.right.right.left,
      factored.right.right.right.right.right.right,
      factored.right.right.right.right.right.left⟩

end BEDC.Derived.MetricUp
