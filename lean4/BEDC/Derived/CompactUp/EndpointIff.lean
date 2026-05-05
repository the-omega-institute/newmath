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

theorem CompactWitnessCarrier_located_finite_refinement_endpoint_package
    {subset located finite intermediate compact finalLocated finalIntermediate finalCompact
      finalFinite finalCompact' : BHist} :
    CompactWitnessCarrier subset located finite intermediate compact ->
      CompactLocatedRefinementChain finite located intermediate compact finalLocated
        finalIntermediate finalCompact ->
        CompactFiniteRefinementChain finite finalCompact finalFinite finalCompact' ->
          CompactWitnessCarrier subset finalLocated finalFinite finalIntermediate finalCompact' ∧
            UnaryHistory finalLocated ∧ UnaryHistory finalIntermediate ∧ UnaryHistory finalFinite ∧
              UnaryHistory finalCompact' ∧
                (hsame finalLocated finalIntermediate ↔ hsame located intermediate) ∧
                  (hsame finalFinite finalCompact' ↔ hsame finite finalCompact) := by
  intro carrier locatedChain finiteChain
  have refinedCarrier :
      CompactWitnessCarrier subset finalLocated finalFinite finalIntermediate finalCompact' :=
    CompactWitnessCarrier_located_finite_refinement_chain_closed carrier locatedChain finiteChain
  have endpoints :
      UnaryHistory finalLocated ∧ UnaryHistory finalIntermediate ∧ UnaryHistory finalFinite ∧
        UnaryHistory finalCompact' :=
    CompactWitnessCarrier_located_finite_refinement_chain_final_endpoints_unary carrier locatedChain
      finiteChain
  have locatedEndpoint :
      hsame finalLocated finalIntermediate ↔ hsame located intermediate :=
    Iff.intro (CompactLocatedRefinementChain_endpoint_hsame_reflects locatedChain)
      (CompactLocatedRefinementChain_endpoint_hsame locatedChain)
  have finiteEndpoint :
      hsame finalFinite finalCompact' ↔ hsame finite finalCompact :=
    CompactFiniteRefinementChain_endpoint_hsame_iff finiteChain
  exact And.intro refinedCarrier
    (And.intro endpoints.left
      (And.intro endpoints.right.left
        (And.intro endpoints.right.right.left
          (And.intro endpoints.right.right.right (And.intro locatedEndpoint finiteEndpoint)))))

end BEDC.Derived.CompactUp
