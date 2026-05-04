import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CompactFiniteRefinementChain_continuation_witness
    {finite compact finalFinite finalCompact : BHist} :
    CompactFiniteRefinementChain finite compact finalFinite finalCompact ->
      exists extra : BHist,
        UnaryHistory extra /\ Cont finite extra finalFinite /\ Cont compact extra finalCompact := by
  intro chain
  induction chain with
  | base =>
      exact Exists.intro BHist.Empty
        (And.intro unary_empty
          (And.intro (cont_right_unit finite) (cont_right_unit compact)))
  | step prior extraCarrier finiteRel compactRel ih =>
      cases ih with
      | intro priorExtra priorData =>
          cases priorData with
          | intro priorExtraCarrier priorRels =>
              cases priorRels with
              | intro finitePrior compactPrior =>
                  cases cont_assoc_left_exists finitePrior finiteRel with
                  | intro combined finiteCombined =>
                      cases finiteCombined with
                      | intro priorCombined finiteFinal =>
                          cases cont_assoc_left_exists compactPrior compactRel with
                          | intro compactCombined compactData =>
                              cases compactData with
                              | intro priorCompactCombined compactFinal =>
                                  have sameCombined : hsame combined compactCombined :=
                                    cont_deterministic priorCombined priorCompactCombined
                                  cases sameCombined
                                  exact Exists.intro combined
                                    (And.intro
                                      (unary_cont_closed priorExtraCarrier extraCarrier
                                        priorCombined)
                                      (And.intro finiteFinal compactFinal))

theorem CompactLocatedRefinementChain_continuation_witness
    {finite located intermediate compact finalLocated finalIntermediate finalCompact : BHist} :
    CompactLocatedRefinementChain finite located intermediate compact finalLocated finalIntermediate
        finalCompact ->
      Cont intermediate finite compact ->
        exists extra : BHist,
          UnaryHistory extra /\ Cont located extra finalLocated /\
            Cont intermediate extra finalIntermediate /\ Cont finalIntermediate finite finalCompact := by
  intro chain initialCompact
  induction chain with
  | base =>
      exact Exists.intro BHist.Empty
        (And.intro unary_empty
          (And.intro (cont_right_unit located)
            (And.intro (cont_right_unit intermediate) initialCompact)))
  | step prior extraCarrier locatedRel intermediateRel compactRel ih =>
      cases ih with
      | intro priorExtra priorData =>
          cases priorData with
          | intro priorExtraCarrier priorRels =>
              cases priorRels with
              | intro locatedPrior rest =>
                  cases rest with
                  | intro intermediatePrior _compactPrior =>
                      cases cont_assoc_left_exists locatedPrior locatedRel with
                      | intro combined locatedCombined =>
                          cases locatedCombined with
                          | intro priorCombined locatedFinal =>
                              cases cont_assoc_left_exists intermediatePrior intermediateRel with
                              | intro intermediateCombined intermediateData =>
                                  cases intermediateData with
                                  | intro priorIntermediateCombined intermediateFinal =>
                                      have sameCombined : hsame combined intermediateCombined :=
                                        cont_deterministic priorCombined
                                          priorIntermediateCombined
                                      cases sameCombined
                                      exact Exists.intro combined
                                        (And.intro
                                          (unary_cont_closed priorExtraCarrier extraCarrier
                                            priorCombined)
                                          (And.intro locatedFinal
                                            (And.intro intermediateFinal compactRel)))

theorem CompactFiniteRefinementChain_common_source_final_finite_deterministic
    {finite compact finalFinite finalCompact finalFinite' finalCompact' : BHist} :
    CompactFiniteRefinementChain finite compact finalFinite finalCompact ->
      CompactFiniteRefinementChain finite compact finalFinite' finalCompact' ->
        hsame finalFinite finalFinite' ->
          (∃ extra : BHist,
            UnaryHistory extra ∧ Cont finite extra finalFinite ∧ Cont compact extra finalCompact) ∧
            hsame finalCompact finalCompact' := by
  intro leftChain rightChain sameFinite
  have leftWitness := CompactFiniteRefinementChain_continuation_witness leftChain
  have rightWitness := CompactFiniteRefinementChain_continuation_witness rightChain
  cases leftWitness with
  | intro leftExtra leftData =>
      cases rightWitness with
      | intro rightExtra rightData =>
          have sameExtra : hsame leftExtra rightExtra := by
            cases sameFinite
            exact cont_left_cancel leftData.right.left rightData.right.left
          have sameCompact : hsame finalCompact finalCompact' := by
            cases sameExtra
            exact cont_deterministic leftData.right.right rightData.right.right
          exact And.intro (Exists.intro leftExtra leftData) sameCompact

end BEDC.Derived.CompactUp
