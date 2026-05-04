import BEDC.Derived.CompactUp.ContinuationWitness

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

theorem CompactLocatedRefinementChain_empty_final_reflects_empty_initial
    {finite located intermediate compact finalLocated finalIntermediate finalCompact : BHist} :
    CompactLocatedRefinementChain finite located intermediate compact finalLocated finalIntermediate
        finalCompact ->
      hsame finalLocated BHist.Empty -> hsame finalIntermediate BHist.Empty ->
        hsame located BHist.Empty ∧ hsame intermediate BHist.Empty := by
  intro chain finalLocatedEmpty finalIntermediateEmpty
  induction chain with
  | base =>
      exact And.intro finalLocatedEmpty finalIntermediateEmpty
  | step prior extraCarrier locatedRel intermediateRel compactRel ih =>
      have locatedEmptyRel := cont_result_hsame_transport locatedRel finalLocatedEmpty
      have intermediateEmptyRel :=
        cont_result_hsame_transport intermediateRel finalIntermediateEmpty
      have locatedParts := cont_empty_result_inversion locatedEmptyRel
      have intermediateParts := cont_empty_result_inversion intermediateEmptyRel
      exact ih locatedParts.left intermediateParts.left

theorem CompactWitnessCarrier_located_empty_final_refinement_reflects_empty_initial
    {subset located finite intermediate compact finalLocated finalIntermediate finalCompact : BHist} :
    CompactWitnessCarrier subset located finite intermediate compact ->
      CompactLocatedRefinementChain finite located intermediate compact finalLocated finalIntermediate
        finalCompact ->
        hsame finalLocated BHist.Empty -> hsame finalIntermediate BHist.Empty ->
          hsame finalCompact BHist.Empty ->
            hsame subset BHist.Empty ∧ hsame located BHist.Empty ∧ hsame finite BHist.Empty ∧
              hsame intermediate BHist.Empty ∧ hsame compact BHist.Empty := by
  intro carrier chain finalLocatedEmpty finalIntermediateEmpty finalCompactEmpty
  cases CompactLocatedRefinementChain_continuation_witness chain carrier.right.right.right.right with
  | intro extra witness =>
      have locatedEmptyRel : Cont located extra BHist.Empty :=
        cont_result_hsame_transport witness.right.left finalLocatedEmpty
      have locatedParts := cont_empty_result_inversion locatedEmptyRel
      have intermediateEmptyRel : Cont intermediate extra BHist.Empty :=
        cont_result_hsame_transport witness.right.right.left finalIntermediateEmpty
      have intermediateParts := cont_empty_result_inversion intermediateEmptyRel
      have finalCompactEmptyRel : Cont finalIntermediate finite BHist.Empty :=
        cont_result_hsame_transport witness.right.right.right finalCompactEmpty
      have finalCompactParts := cont_empty_result_inversion finalCompactEmptyRel
      have subsetEmptyRel : Cont subset located BHist.Empty :=
        cont_result_hsame_transport carrier.right.right.right.left intermediateParts.left
      have subsetParts := cont_empty_result_inversion subsetEmptyRel
      have compactEmpty : hsame compact BHist.Empty := by
        cases intermediateParts.left
        cases finalCompactParts.right
        exact cont_deterministic carrier.right.right.right.right (cont_right_unit BHist.Empty)
      exact And.intro subsetParts.left
        (And.intro locatedParts.left
          (And.intro finalCompactParts.right
            (And.intro intermediateParts.left compactEmpty)))

end BEDC.Derived.CompactUp
