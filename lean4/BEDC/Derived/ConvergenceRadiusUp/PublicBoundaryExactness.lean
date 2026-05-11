import BEDC.Derived.ConvergenceRadiusUp

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ConvRad_public_boundary_exactness {a b : Nat -> BHist} {z0 R R' : BHist} :
    ConvRadCheckedRowReduct a z0 R -> ConvRadRadiusClassifierSpec a b R R' ->
      ConvRadCheckedRowReduct b z0 R' ∧ hsame R R' ∧ UnaryHistory R' := by
  intro checked classifier
  have targetCarrier : PowerSeriesCarrier b z0 :=
    (PowerSeriesCarrier_origin_coefficient_transport (hsame_refl z0)
      classifier.right.right.right checked.left.left).right
  have targetRadius : ConvRad b R' :=
    (ConvRad_radius_coefficient_classifier_transport classifier.right.left
      classifier.right.right.left classifier.right.right.right checked.left.right).right
  have targetSource : ConvRadSourceSpec b z0 R' :=
    And.intro targetCarrier targetRadius
  exact And.intro
    (ConvRadSourceSpec_checkedRowReduct_readback targetSource)
    (And.intro classifier.right.left classifier.right.right.left)

end BEDC.Derived.ConvergenceRadiusUp
