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

end BEDC.Derived.RiemannianMetricUp
