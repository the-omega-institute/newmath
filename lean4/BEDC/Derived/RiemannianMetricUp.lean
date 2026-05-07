import BEDC.Derived.InnerProductUp
import BEDC.Derived.ManifoldUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RiemannianMetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.InnerProductUp
open BEDC.Derived.ManifoldUp
open BEDC.Derived.VecSpaceUp

def RiemannianMetricSingletonFibreSurface (point tangent metric : BHist) : Prop :=
  ManifoldSingletonCarrier point ∧ VecSpaceSingletonCarrier tangent ∧
    InnerProductSingletonOrthogonal tangent tangent ∧
      hsame metric (InnerProductSingletonForm tangent tangent)

theorem RiemannianMetricSingletonFibreSurface_carrier_rows {point tangent metric : BHist} :
    RiemannianMetricSingletonFibreSurface point tangent metric ->
      ManifoldSingletonCarrier point ∧ VecSpaceSingletonCarrier tangent ∧
        InnerProductSingletonOrthogonal tangent tangent ∧
          hsame metric (InnerProductSingletonForm tangent tangent) ∧
            UnaryHistory point ∧ UnaryHistory tangent ∧ Cont BHist.Empty point point := by
  intro surface
  have pointRows := ManifoldSingletonCarrier_topology_scope surface.left
  have tangentUnary : UnaryHistory tangent :=
    unary_transport unary_empty (hsame_symm surface.right.left)
  exact And.intro surface.left
    (And.intro surface.right.left
      (And.intro surface.right.right.left
        (And.intro surface.right.right.right
            (And.intro pointRows.right.left
            (And.intro tangentUnary pointRows.right.right)))))

theorem RiemannianMetricSingletonFibreSurface_fibrewise_compatibility_scope
    {point point' tangent tangent' metric metric' sourceDomain targetDomain sourceCoord
      targetCoord : BHist} :
    RiemannianMetricSingletonFibreSurface point tangent metric ->
      RiemannianMetricSingletonFibreSurface point' tangent' metric' ->
        hsame point point' ->
          Cont BHist.Empty point sourceDomain ->
            Cont BHist.Empty point' targetDomain ->
              Cont BHist.Empty point sourceCoord ->
                Cont BHist.Empty point' targetCoord ->
                  InnerProductSingletonOrthogonal tangent tangent ∧
                    InnerProductSingletonOrthogonal tangent' tangent' ∧
                      hsame metric metric' ∧ hsame sourceDomain targetDomain ∧
                        hsame sourceCoord targetCoord ∧ UnaryHistory sourceCoord ∧
                          UnaryHistory targetCoord := by
  intro surface surface' samePoints sourceDomainRow targetDomainRow sourceCoordRow targetCoordRow
  have pointRows := ManifoldSingletonCarrier_topology_scope surface.left
  have pointRows' := ManifoldSingletonCarrier_topology_scope surface'.left
  have domainCoordRows :=
    ManifoldSingleton_chart_coordinate_carrier_transport
      pointRows.right.left pointRows'.right.left samePoints sourceDomainRow targetDomainRow
      sourceCoordRow targetCoordRow
  have sameMetricForm :
      hsame (InnerProductSingletonForm tangent tangent)
        (InnerProductSingletonForm tangent' tangent') := by
    unfold InnerProductSingletonForm
    exact hsame_refl (BHist.e1 (BHist.e1 BHist.Empty))
  have sameMetric : hsame metric metric' :=
    hsame_trans surface.right.right.right
      (hsame_trans sameMetricForm (hsame_symm surface'.right.right.right))
  have sameSourceCoordPoint : hsame sourceCoord point :=
    cont_left_unit_result sourceCoordRow
  have sourceCoordEmpty : hsame sourceCoord BHist.Empty :=
    hsame_trans sameSourceCoordPoint pointRows.left
  have sourceCoordUnary : UnaryHistory sourceCoord :=
    unary_transport unary_empty (hsame_symm sourceCoordEmpty)
  have sameTargetCoordPoint : hsame targetCoord point' :=
    cont_left_unit_result targetCoordRow
  have targetCoordEmpty : hsame targetCoord BHist.Empty :=
    hsame_trans sameTargetCoordPoint pointRows'.left
  have targetCoordUnary : UnaryHistory targetCoord :=
    unary_transport unary_empty (hsame_symm targetCoordEmpty)
  exact And.intro surface.right.right.left
    (And.intro surface'.right.right.left
      (And.intro sameMetric
        (And.intro domainCoordRows.left
          (And.intro domainCoordRows.right
            (And.intro sourceCoordUnary targetCoordUnary)))))

end BEDC.Derived.RiemannianMetricUp
