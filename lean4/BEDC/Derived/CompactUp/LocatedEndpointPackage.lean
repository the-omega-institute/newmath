import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CompactLocatedRefinementChain_endpoint_unary_hsame_iff
    {finite located intermediate compact finalLocated finalIntermediate finalCompact : BHist} :
    CompactLocatedRefinementChain finite located intermediate compact finalLocated finalIntermediate
        finalCompact ->
      UnaryHistory finite -> UnaryHistory located -> UnaryHistory intermediate ->
        UnaryHistory compact ->
        UnaryHistory finalLocated ∧ UnaryHistory finalIntermediate ∧
          UnaryHistory finalCompact ∧
          (hsame finalLocated finalIntermediate <-> hsame located intermediate) := by
  intro chain finiteCarrier locatedCarrier intermediateCarrier compactCarrier
  have endpointCarriers :=
    CompactLocatedRefinementChain_final_endpoints_unary chain finiteCarrier locatedCarrier
      intermediateCarrier compactCarrier
  exact And.intro endpointCarriers.left
    (And.intro endpointCarriers.right.left
      (And.intro endpointCarriers.right.right
        (Iff.intro (CompactLocatedRefinementChain_endpoint_hsame_reflects chain)
          (CompactLocatedRefinementChain_endpoint_hsame chain))))

end BEDC.Derived.CompactUp
