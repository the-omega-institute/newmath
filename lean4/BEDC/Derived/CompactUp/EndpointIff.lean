import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CompactFiniteRefinementChain_endpoint_hsame_iff
    {finite compact finalFinite finalCompact : BHist} :
    CompactFiniteRefinementChain finite compact finalFinite finalCompact ->
      (hsame finalFinite finalCompact ↔ hsame finite compact) := by
  intro chain
  exact Iff.intro (CompactFiniteRefinementChain_endpoint_hsame_reflects chain)
    (CompactFiniteRefinementChain_endpoint_hsame chain)

theorem CompactWitnessCarrier_finite_refinement_endpoint_package
    {subset located finite intermediate compact finalFinite finalCompact : BHist} :
    CompactWitnessCarrier subset located finite intermediate compact ->
      CompactFiniteRefinementChain finite compact finalFinite finalCompact ->
        UnaryHistory finalFinite ∧ UnaryHistory finalCompact ∧
          (hsame finalFinite finalCompact ↔ hsame finite compact) := by
  intro carrier chain
  have endpoints :=
    CompactWitnessCarrier_finite_refinement_chain_endpoints_unary carrier chain
  exact And.intro endpoints.left
    (And.intro endpoints.right (CompactFiniteRefinementChain_endpoint_hsame_iff chain))

end BEDC.Derived.CompactUp
