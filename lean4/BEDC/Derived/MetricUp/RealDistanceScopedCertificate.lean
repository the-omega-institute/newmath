import BEDC.Derived.MetricUp.RealAlgOrderPositiveDistancePublicCorrespondence

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MetricspaceRealDistanceScopedCertificate
    {x y dist radius witness budget classifier provenance realAlg positiveRead : BHist} :
    MetricspaceRealDistanceCarrier x y dist radius witness budget classifier provenance realAlg →
      Cont radius realAlg positiveRead →
        MetricDistanceWitness x y dist ∧ UnaryHistory radius ∧ UnaryHistory positiveRead ∧
          Cont dist radius budget ∧ Cont radius realAlg positiveRead ∧ hsame classifier dist ∧
            Cont witness budget provenance := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory MetricDistanceWitness
  intro carrier positiveRoute
  have publicRows :=
    MetricspaceRealDistanceCarrier_public_law_package carrier
  have positiveRows :=
    MetricspaceRealalgorderPositiveDistancePublicCorrespondence carrier positiveRoute
  have positiveReadUnary : UnaryHistory positiveRead :=
    positiveRows.right.right.right.right.right.left
  exact
    ⟨publicRows.left, publicRows.right.left, positiveReadUnary,
      publicRows.right.right.left, positiveRoute, publicRows.right.right.right.left,
      publicRows.right.right.right.right⟩

end BEDC.Derived.MetricUp
