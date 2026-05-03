import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CompactFiniteRefinementChain_empty_final_reflects_empty_initial
    {finite compact finalFinite finalCompact : BHist} :
    CompactFiniteRefinementChain finite compact finalFinite finalCompact ->
      hsame finalFinite BHist.Empty -> hsame finalCompact BHist.Empty ->
        hsame finite BHist.Empty ∧ hsame compact BHist.Empty := by
  intro chain finalFiniteEmpty finalCompactEmpty
  induction chain with
  | base =>
      exact And.intro finalFiniteEmpty finalCompactEmpty
  | step prior extraCarrier finiteRel compactRel ih =>
      have finiteEmptyRel := cont_result_hsame_transport finiteRel finalFiniteEmpty
      have compactEmptyRel := cont_result_hsame_transport compactRel finalCompactEmpty
      have finiteEmpty := (cont_empty_result_inversion finiteEmptyRel).left
      have compactEmpty := (cont_empty_result_inversion compactEmptyRel).left
      exact ih finiteEmpty compactEmpty

theorem CompactWitnessCarrier_empty_final_refinement_reflects_empty_initial
    {subset located finite intermediate compact finalFinite finalCompact : BHist} :
    CompactWitnessCarrier subset located finite intermediate compact ->
      CompactFiniteRefinementChain finite compact finalFinite finalCompact ->
        hsame finalFinite BHist.Empty -> hsame finalCompact BHist.Empty ->
          hsame subset BHist.Empty ∧ hsame located BHist.Empty ∧ hsame finite BHist.Empty ∧
            hsame intermediate BHist.Empty ∧ hsame compact BHist.Empty := by
  intro carrier chain finalFiniteEmpty finalCompactEmpty
  have initialEmpty :=
    CompactFiniteRefinementChain_empty_final_reflects_empty_initial chain finalFiniteEmpty
      finalCompactEmpty
  have compactEmptyRel : Cont intermediate finite BHist.Empty :=
    cont_result_hsame_transport carrier.right.right.right.right initialEmpty.right
  have compactParts := cont_empty_result_inversion compactEmptyRel
  have locatedEmptyRel : Cont subset located BHist.Empty :=
    cont_result_hsame_transport carrier.right.right.right.left compactParts.left
  have locatedParts := cont_empty_result_inversion locatedEmptyRel
  exact And.intro locatedParts.left
    (And.intro locatedParts.right
      (And.intro initialEmpty.left (And.intro compactParts.left initialEmpty.right)))

end BEDC.Derived.CompactUp
