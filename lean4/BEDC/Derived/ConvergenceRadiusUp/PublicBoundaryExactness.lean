import BEDC.Derived.ConvergenceRadiusUp

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem ConvRadSourceSpec_public_boundary_exactness {a : Nat -> BHist} {z0 R : BHist} :
    ConvRadSourceSpec a z0 R ->
      SemanticNameCert (ConvRad a) (ConvRad a) (ConvRad a) hsame ∧
        ConvRadCheckedRowReduct a z0 R := by
  intro source
  exact And.intro
    (ConvRad_semanticNameCert source.right)
    (ConvRadSourceSpec_checkedRowReduct_readback source)

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

theorem ConvRadCheckedRowReduct_public_boundary_exactness {a : Nat -> BHist} {z0 R : BHist} :
    ConvRadCheckedRowReduct a z0 R ->
      PowerSeriesCarrier a z0 ∧ ConvRad a R ∧ UnaryHistory R ∧
        (∃ K : BHist -> BHist, ∀ {r : BHist}, UnaryHistory r -> Cont r (K r) R ->
          PowerSeriesCarrier a z0 ∧ GeomBound a r (K r) ∧ UnaryHistory R) := by
  intro checked
  exact And.intro checked.left.left
    (And.intro checked.left.right
      (And.intro checked.left.right.left checked.right))

end BEDC.Derived.ConvergenceRadiusUp
