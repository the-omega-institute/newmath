import BEDC.Derived.InnerProductUp
import BEDC.Derived.ManifoldUp
import BEDC.Derived.RealUp.Core
import BEDC.Derived.VecSpaceUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RiemannianMetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.InnerProductUp
open BEDC.Derived.ManifoldUp
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp

theorem RiemannianMetricSingleton_source_fibre_carrier_row {x u v metric : BHist} :
    ManifoldSingletonCarrier x ->
      VecSpaceSingletonCarrier u ->
        VecSpaceSingletonCarrier v ->
          hsame metric (InnerProductSingletonForm u v) ->
            ManifoldSingletonCarrier x ∧ VecSpaceSingletonCarrier u ∧
              VecSpaceSingletonCarrier v ∧
                RealConstantHistoryClassifier metric (BHist.e1 (BHist.e1 BHist.Empty)) ∧
                  UnaryHistory x ∧ UnaryHistory u ∧ UnaryHistory v := by
  intro pointCarrier sourceCarrier targetCarrier metricDisplayed
  have pointUnary : UnaryHistory x :=
    (ManifoldSingletonCarrier_topology_scope pointCarrier).right.left
  have sourceUnary : UnaryHistory u :=
    unary_transport unary_empty (hsame_symm sourceCarrier)
  have targetUnary : UnaryHistory v :=
    unary_transport unary_empty (hsame_symm targetCarrier)
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    RatHistoryClassifier_e1_tail_unary_iff.mpr
      (And.intro unary_empty (And.intro unary_empty (hsame_refl BHist.Empty)))
  have displayedClassifier :
      RealConstantHistoryClassifier (InnerProductSingletonForm u v)
        (BHist.e1 (BHist.e1 BHist.Empty)) := by
    unfold InnerProductSingletonForm
    exact RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier
  have metricClassifier :
      RealConstantHistoryClassifier metric (BHist.e1 (BHist.e1 BHist.Empty)) :=
    RealConstantHistoryClassifier_endpoint_transport (hsame_symm metricDisplayed)
      (hsame_refl (BHist.e1 (BHist.e1 BHist.Empty))) displayedClassifier
  exact And.intro pointCarrier
    (And.intro sourceCarrier
      (And.intro targetCarrier
        (And.intro metricClassifier
          (And.intro pointUnary (And.intro sourceUnary targetUnary)))))

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

theorem RiemannianMetricSingletonFibreSurface_classifier_stability
    {point point' tangent tangent' metric metric' : BHist} :
    RiemannianMetricSingletonFibreSurface point tangent metric ->
      hsame point point' -> hsame tangent tangent' -> hsame metric metric' ->
        RiemannianMetricSingletonFibreSurface point' tangent' metric' ∧
          ManifoldSingletonCarrier point' ∧ VecSpaceSingletonCarrier tangent' ∧
            RealConstantHistoryClassifier metric' (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro surface samePoint sameTangent sameMetric
  cases samePoint
  cases sameTangent
  cases sameMetric
  have rows :
      ManifoldSingletonCarrier point ∧ VecSpaceSingletonCarrier tangent ∧
        VecSpaceSingletonCarrier tangent ∧
          RealConstantHistoryClassifier metric (BHist.e1 (BHist.e1 BHist.Empty)) ∧
            UnaryHistory point ∧ UnaryHistory tangent ∧ UnaryHistory tangent :=
    RiemannianMetricSingleton_source_fibre_carrier_row surface.left surface.right.left
      surface.right.left surface.right.right.right
  exact And.intro surface
    (And.intro rows.left (And.intro rows.right.left rows.right.right.right.left))

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

theorem RiemannianMetricPublicSourceFibre_name_certificate
    {point point' tangent tangent' metric metric' sourceDomain targetDomain sourceCoord
      targetCoord : BHist} :
    RiemannianMetricSingletonFibreSurface point tangent metric ->
      RiemannianMetricSingletonFibreSurface point' tangent' metric' ->
        hsame point point' ->
          Cont BHist.Empty point sourceDomain ->
            Cont BHist.Empty point' targetDomain ->
              Cont BHist.Empty point sourceCoord ->
                Cont BHist.Empty point' targetCoord ->
                  ManifoldSingletonCarrier point ∧ VecSpaceSingletonCarrier tangent ∧
                    InnerProductSingletonOrthogonal tangent tangent ∧ hsame metric metric' ∧
                      hsame sourceDomain targetDomain ∧ UnaryHistory sourceCoord ∧
                        UnaryHistory targetCoord := by
  intro surface surface' samePoints sourceDomainRow targetDomainRow sourceCoordRow targetCoordRow
  have carrierRows := RiemannianMetricSingletonFibreSurface_carrier_rows surface
  have compatibilityRows :=
    RiemannianMetricSingletonFibreSurface_fibrewise_compatibility_scope surface surface'
      samePoints sourceDomainRow targetDomainRow sourceCoordRow targetCoordRow
  exact And.intro carrierRows.left
    (And.intro carrierRows.right.left
      (And.intro carrierRows.right.right.left
        (And.intro compatibilityRows.right.right.left
          (And.intro compatibilityRows.right.right.right.left
            (And.intro compatibilityRows.right.right.right.right.right.left
              compatibilityRows.right.right.right.right.right.right)))))

end BEDC.Derived.RiemannianMetricUp
