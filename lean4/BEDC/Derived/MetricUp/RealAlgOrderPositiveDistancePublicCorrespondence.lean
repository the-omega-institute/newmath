import BEDC.Derived.MetricUp.RealDistancePublicLawPackage

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MetricspaceRealalgorderPositiveDistancePublicCorrespondence
    {x y dist radius witness budget classifier provenance realAlg positiveRead : BHist} :
    MetricspaceRealDistanceCarrier x y dist radius witness budget classifier provenance realAlg →
      Cont radius realAlg positiveRead →
        MetricDistanceWitness x y dist ∧ UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory dist ∧
          UnaryHistory radius ∧ UnaryHistory positiveRead ∧
            Cont radius realAlg positiveRead ∧ Cont dist radius budget ∧
              hsame classifier dist := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame
  intro carrier radiusRealAlgPositive
  rcases carrier with
    ⟨distanceWitness, radiusUnary, distRadiusBudget, classifierSame, _witnessBudgetProvenance,
      realAlgUnary⟩
  have positiveReadUnary : UnaryHistory positiveRead :=
    unary_cont_closed radiusUnary realAlgUnary radiusRealAlgPositive
  exact
    ⟨distanceWitness, distanceWitness.left, distanceWitness.right.left,
      distanceWitness.right.right.left, radiusUnary, positiveReadUnary, radiusRealAlgPositive,
      distRadiusBudget, classifierSame⟩

end BEDC.Derived.MetricUp
