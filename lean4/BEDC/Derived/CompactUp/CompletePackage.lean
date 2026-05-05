import BEDC.Derived.CompactUp.EndpointIff
import BEDC.Derived.CompactUp.EmptyFinalReflection
import BEDC.Derived.CompactUp.NonemptyForward

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CompactWitnessCarrier_located_finite_refinement_complete_package
    {subset located finite intermediate compact finalLocated finalIntermediate finalCompact
      finalFinite finalCompact' : BHist} :
    CompactWitnessCarrier subset located finite intermediate compact ->
      CompactLocatedRefinementChain finite located intermediate compact finalLocated finalIntermediate
        finalCompact ->
      CompactFiniteRefinementChain finite finalCompact finalFinite finalCompact' ->
        CompactWitnessCarrier subset finalLocated finalFinite finalIntermediate finalCompact' ∧
          UnaryHistory finalLocated ∧ UnaryHistory finalIntermediate ∧ UnaryHistory finalFinite ∧
          UnaryHistory finalCompact' ∧
          (hsame finalLocated finalIntermediate ↔ hsame located intermediate) ∧
          (hsame finalFinite finalCompact' ↔ hsame finite finalCompact) ∧
          ((hsame finalLocated BHist.Empty -> hsame finalIntermediate BHist.Empty ->
            hsame finalFinite BHist.Empty -> hsame finalCompact' BHist.Empty ->
              hsame subset BHist.Empty ∧ hsame located BHist.Empty ∧ hsame finite BHist.Empty ∧
                hsame intermediate BHist.Empty ∧ hsame compact BHist.Empty)) ∧
          ((hsame located BHist.Empty -> False) -> hsame finalLocated BHist.Empty -> False) ∧
          ((hsame intermediate BHist.Empty -> False) -> hsame finalIntermediate BHist.Empty -> False) ∧
          ((hsame finite BHist.Empty -> False) -> hsame finalFinite BHist.Empty -> False) ∧
          ((hsame finalCompact BHist.Empty -> False) -> hsame finalCompact' BHist.Empty -> False) := by
  intro carrier locatedChain finiteChain
  have endpointPackage :=
    CompactWitnessCarrier_located_finite_refinement_endpoint_package carrier locatedChain
      finiteChain
  have emptyReflection :=
    CompactWitnessCarrier_located_finite_empty_final_reflects_empty_initial carrier locatedChain
      finiteChain
  exact And.intro endpointPackage.left
    (And.intro endpointPackage.right.left
      (And.intro endpointPackage.right.right.left
        (And.intro endpointPackage.right.right.right.left
          (And.intro endpointPackage.right.right.right.right.left
            (And.intro endpointPackage.right.right.right.right.right.left
              (And.intro endpointPackage.right.right.right.right.right.right
                (And.intro emptyReflection
                  (And.intro (CompactLocatedRefinementChain_located_nonempty_forward locatedChain)
                    (And.intro
                      (CompactLocatedRefinementChain_intermediate_nonempty_forward locatedChain)
                      (And.intro (CompactFiniteRefinementChain_nonempty_forward finiteChain)
                        (CompactFiniteRefinementChain_compact_nonempty_forward finiteChain)))))))))))

end BEDC.Derived.CompactUp
