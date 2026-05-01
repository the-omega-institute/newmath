import BEDC.FKernel.Unary
import BEDC.FKernel.Cont

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def CompactWitnessCarrier (subset located finite intermediate compact : BHist) : Prop :=
  UnaryHistory subset ∧ UnaryHistory located ∧ UnaryHistory finite ∧
    Cont subset located intermediate ∧ Cont intermediate finite compact

theorem CompactWitnessCarrier_finite_extension_closed
    {subset located finite extra intermediate compact newFinite extended : BHist} :
    CompactWitnessCarrier subset located finite intermediate compact -> UnaryHistory extra ->
      Cont finite extra newFinite -> Cont compact extra extended ->
        CompactWitnessCarrier subset located newFinite intermediate extended := by
  intro carrier extraCarrier finiteExtra compactExtra
  cases carrier with
  | intro subsetCarrier rest =>
      cases rest with
      | intro locatedCarrier rest =>
          cases rest with
          | intro finiteCarrier rest =>
              cases rest with
              | intro locatedLedger finiteLedger =>
                  have newFiniteCarrier : UnaryHistory newFinite :=
                    unary_cont_closed finiteCarrier extraCarrier finiteExtra
                  have associated := cont_assoc_left_exists finiteLedger compactExtra
                  cases associated with
                  | intro joined joinedData =>
                      cases joinedData with
                      | intro joinedLedger extendedLedger =>
                          have sameJoined : hsame newFinite joined :=
                            cont_deterministic finiteExtra joinedLedger
                          cases sameJoined
                          exact
                            And.intro subsetCarrier
                              (And.intro locatedCarrier
                                (And.intro newFiniteCarrier
                                  (And.intro locatedLedger extendedLedger)))

inductive CompactFiniteRefinementChain : BHist -> BHist -> BHist -> BHist -> Prop where
  | base {finite compact : BHist} :
      CompactFiniteRefinementChain finite compact finite compact
  | step {finite compact currentFinite currentCompact extra nextFinite nextCompact : BHist} :
      CompactFiniteRefinementChain finite compact currentFinite currentCompact ->
        UnaryHistory extra -> Cont currentFinite extra nextFinite ->
          Cont currentCompact extra nextCompact ->
            CompactFiniteRefinementChain finite compact nextFinite nextCompact

theorem CompactFiniteRefinementChain_transitivity
    {finite compact midFinite midCompact finalFinite finalCompact : BHist} :
    CompactFiniteRefinementChain finite compact midFinite midCompact ->
      CompactFiniteRefinementChain midFinite midCompact finalFinite finalCompact ->
        CompactFiniteRefinementChain finite compact finalFinite finalCompact := by
  intro first second
  induction second with
  | base =>
      exact first
  | step prior extraCarrier finiteRel compactRel ih =>
      exact CompactFiniteRefinementChain.step ih extraCarrier finiteRel compactRel

theorem CompactFiniteRefinementChain_final_endpoints_unary
    {finite compact finalFinite finalCompact : BHist} :
    CompactFiniteRefinementChain finite compact finalFinite finalCompact →
      UnaryHistory finite → UnaryHistory compact →
        UnaryHistory finalFinite ∧ UnaryHistory finalCompact := by
  intro chain finiteCarrier compactCarrier
  induction chain with
  | base =>
      exact And.intro finiteCarrier compactCarrier
  | step prior extraCarrier finiteRel compactRel ih =>
      cases ih with
      | intro currentFiniteCarrier currentCompactCarrier =>
          exact And.intro
            (unary_cont_closed currentFiniteCarrier extraCarrier finiteRel)
            (unary_cont_closed currentCompactCarrier extraCarrier compactRel)

theorem CompactWitnessCarrier_finite_refinement_chain_closed
    {subset located finite intermediate compact finalFinite finalCompact : BHist} :
    CompactWitnessCarrier subset located finite intermediate compact ->
      CompactFiniteRefinementChain finite compact finalFinite finalCompact ->
        CompactWitnessCarrier subset located finalFinite intermediate finalCompact := by
  intro carrier chain
  induction chain with
  | base => exact carrier
  | step prior extraCarrier finiteRel compactRel ih =>
      exact CompactWitnessCarrier_finite_extension_closed ih extraCarrier finiteRel compactRel

def CompactNetWitness (center precision net : BHist) : Prop :=
  UnaryHistory center ∧ UnaryHistory precision ∧ UnaryHistory net ∧ Cont center precision net

theorem CompactNetWitness_prefix_closed {p center precision net : BHist} :
    UnaryHistory p -> CompactNetWitness center precision net ->
      CompactNetWitness (append p center) precision (append p net) := by
  intro prefixCarrier witness
  cases witness with
  | intro centerCarrier rest =>
      cases rest with
      | intro precisionCarrier rest =>
          cases rest with
          | intro netCarrier netRel =>
              cases netRel
              exact
                And.intro
                  (unary_append_closed prefixCarrier centerCarrier)
                  (And.intro precisionCarrier
                    (And.intro
                      (unary_append_closed prefixCarrier
                        (unary_cont_closed centerCarrier precisionCarrier (cont_intro rfl)))
                      (cont_intro (append_assoc p center precision).symm)))

theorem CompactWitnessCarrier_located_extension_closed
    {subset located finite extra intermediate compact newLocated newIntermediate extended : BHist} :
    CompactWitnessCarrier subset located finite intermediate compact -> UnaryHistory extra ->
      Cont located extra newLocated -> Cont intermediate extra newIntermediate ->
        Cont newIntermediate finite extended ->
          CompactWitnessCarrier subset newLocated finite newIntermediate extended := by
  intro carrier extraCarrier locatedExtra intermediateExtra extendedLedger
  cases carrier with
  | intro subsetCarrier rest =>
      cases rest with
      | intro locatedCarrier rest =>
          cases rest with
          | intro finiteCarrier rest =>
              cases rest with
              | intro locatedLedger _compactLedger =>
                  have newLocatedCarrier : UnaryHistory newLocated :=
                    unary_cont_closed locatedCarrier extraCarrier locatedExtra
                  have associated := cont_assoc_left_exists locatedLedger intermediateExtra
                  cases associated with
                  | intro shifted shiftedData =>
                      cases shiftedData with
                      | intro shiftedLocated subsetShifted =>
                          have sameShifted : hsame newLocated shifted :=
                            cont_deterministic locatedExtra shiftedLocated
                          cases sameShifted
                          exact
                            And.intro subsetCarrier
                              (And.intro newLocatedCarrier
                                (And.intro finiteCarrier
                                  (And.intro subsetShifted extendedLedger)))

inductive CompactLocatedRefinementChain :
    BHist -> BHist -> BHist -> BHist -> BHist -> BHist -> BHist -> Prop where
  | base {finite located intermediate compact : BHist} :
      CompactLocatedRefinementChain finite located intermediate compact located intermediate compact
  | step
      {finite located intermediate compact currentLocated currentIntermediate currentCompact extra
        nextLocated nextIntermediate nextCompact : BHist} :
      CompactLocatedRefinementChain finite located intermediate compact currentLocated
        currentIntermediate currentCompact ->
      UnaryHistory extra -> Cont currentLocated extra nextLocated ->
        Cont currentIntermediate extra nextIntermediate ->
          Cont nextIntermediate finite nextCompact ->
          CompactLocatedRefinementChain finite located intermediate compact nextLocated
            nextIntermediate nextCompact

theorem CompactLocatedRefinementChain_transitivity
    {finite located intermediate compact midLocated midIntermediate midCompact finalLocated
      finalIntermediate finalCompact : BHist} :
    CompactLocatedRefinementChain finite located intermediate compact midLocated midIntermediate
        midCompact ->
      CompactLocatedRefinementChain finite midLocated midIntermediate midCompact finalLocated
        finalIntermediate finalCompact ->
        CompactLocatedRefinementChain finite located intermediate compact finalLocated finalIntermediate
          finalCompact := by
  intro first second
  induction second with
  | base =>
      exact first
  | step prior extraCarrier locatedRel intermediateRel compactRel ih =>
      exact CompactLocatedRefinementChain.step ih extraCarrier locatedRel intermediateRel compactRel

theorem CompactLocatedRefinementChain_final_endpoints_unary
    {finite located intermediate compact finalLocated finalIntermediate finalCompact : BHist} :
    CompactLocatedRefinementChain finite located intermediate compact finalLocated finalIntermediate
        finalCompact →
      UnaryHistory finite → UnaryHistory located → UnaryHistory intermediate → UnaryHistory compact →
        UnaryHistory finalLocated ∧ UnaryHistory finalIntermediate ∧ UnaryHistory finalCompact := by
  intro chain finiteCarrier locatedCarrier intermediateCarrier compactCarrier
  induction chain with
  | base =>
      exact And.intro locatedCarrier (And.intro intermediateCarrier compactCarrier)
  | step prior extraCarrier locatedRel intermediateRel compactRel ih =>
      cases ih with
      | intro currentLocatedCarrier rest =>
          cases rest with
          | intro currentIntermediateCarrier _currentCompactCarrier =>
              have nextIntermediateCarrier :=
                unary_cont_closed currentIntermediateCarrier extraCarrier intermediateRel
              exact And.intro
                (unary_cont_closed currentLocatedCarrier extraCarrier locatedRel)
                (And.intro nextIntermediateCarrier
                  (unary_cont_closed nextIntermediateCarrier finiteCarrier compactRel))

theorem CompactWitnessCarrier_located_refinement_chain_closed
    {subset finite located intermediate compact finalLocated finalIntermediate finalCompact : BHist} :
    CompactWitnessCarrier subset located finite intermediate compact ->
      CompactLocatedRefinementChain finite located intermediate compact finalLocated finalIntermediate
        finalCompact ->
        CompactWitnessCarrier subset finalLocated finite finalIntermediate finalCompact := by
  intro carrier chain
  induction chain with
  | base => exact carrier
  | step prior extraCarrier locatedRel intermediateRel compactRel ih =>
      exact
        CompactWitnessCarrier_located_extension_closed ih extraCarrier locatedRel intermediateRel
          compactRel

theorem CompactNetWitness_prefix_iff {p center precision net : BHist} :
    CompactNetWitness (append p center) precision (append p net) ↔
      UnaryHistory p ∧ CompactNetWitness center precision net := by
  constructor
  · intro witness
    cases witness with
    | intro prefixedCenter rest =>
        cases rest with
        | intro precisionCarrier rest =>
            cases rest with
            | intro prefixedNet netRel =>
                exact
                  And.intro (unary_append_left_factor prefixedCenter)
                    (And.intro (unary_append_right_factor prefixedCenter)
                      (And.intro precisionCarrier
                        (And.intro (unary_append_right_factor prefixedNet)
                          (cont_prefix_cancel netRel))))
  · intro prefixed
    cases prefixed with
    | intro prefixCarrier witness =>
        exact CompactNetWitness_prefix_closed prefixCarrier witness

theorem CompactNetWitness_prefixed_composite_closed
    {p center precision extra composite net refined : BHist} :
    UnaryHistory p -> CompactNetWitness center precision net ->
      CompactNetWitness net extra refined -> Cont precision extra composite ->
        CompactNetWitness (append p center) composite (append p refined) := by
  intro prefixCarrier first second compositeRel
  cases first with
  | intro centerCarrier firstRest =>
      cases firstRest with
      | intro precisionCarrier firstRest =>
          cases firstRest with
          | intro _netCarrier firstRel =>
              cases second with
              | intro _netCarrier' secondRest =>
                  cases secondRest with
                  | intro extraCarrier secondRest =>
                      cases secondRest with
                      | intro refinedCarrier secondRel =>
                          have compositeCarrier : UnaryHistory composite :=
                            unary_cont_closed precisionCarrier extraCarrier compositeRel
                          cases firstRel
                          cases secondRel
                          cases compositeRel
                          exact
                            And.intro (unary_append_closed prefixCarrier centerCarrier)
                              (And.intro compositeCarrier
                                (And.intro (unary_append_closed prefixCarrier refinedCarrier)
                                  (cont_intro
                                    ((congrArg (append p)
                                      (append_assoc center precision extra)).trans
                                      (append_assoc p center (append precision extra)).symm))))

theorem CompactNetWitness_prefixed_composite_factorizes
    {p center precision extra composite refined : BHist} :
    UnaryHistory precision -> UnaryHistory extra -> Cont precision extra composite ->
      CompactNetWitness (append p center) composite (append p refined) ->
        ∃ net : BHist, CompactNetWitness center precision net ∧
          CompactNetWitness net extra refined := by
  intro precisionCarrier extraCarrier compositeRel prefixedWitness
  have unprefixed := (CompactNetWitness_prefix_iff.mp prefixedWitness).right
  cases unprefixed with
  | intro centerCarrier rest =>
      cases rest with
      | intro _compositeCarrier rest =>
          cases rest with
          | intro refinedCarrier refinedRel =>
              let net := append center precision
              have netCarrier : UnaryHistory net :=
                unary_append_closed centerCarrier precisionCarrier
              have firstWitness : CompactNetWitness center precision net :=
                And.intro centerCarrier
                  (And.intro precisionCarrier (And.intro netCarrier (cont_intro rfl)))
              have secondRel : Cont net extra refined := by
                cases refinedRel
                cases compositeRel
                exact cont_intro (append_assoc center precision extra).symm
              have secondWitness : CompactNetWitness net extra refined :=
                And.intro netCarrier
                  (And.intro extraCarrier (And.intro refinedCarrier secondRel))
              exact Exists.intro net (And.intro firstWitness secondWitness)

theorem CompactNetWitness_prefixed_composite_iff
    {p center precision extra composite refined : BHist} :
    UnaryHistory precision -> UnaryHistory extra -> Cont precision extra composite ->
      (CompactNetWitness (append p center) composite (append p refined) ↔
        UnaryHistory p ∧ ∃ net : BHist, CompactNetWitness center precision net ∧
          CompactNetWitness net extra refined) := by
  intro precisionCarrier extraCarrier compositeRel
  constructor
  · intro prefixedWitness
    exact
      And.intro (CompactNetWitness_prefix_iff.mp prefixedWitness).left
        (CompactNetWitness_prefixed_composite_factorizes precisionCarrier extraCarrier
          compositeRel prefixedWitness)
  · intro data
    cases data with
    | intro prefixCarrier witness =>
        cases witness with
        | intro net witnessData =>
            cases witnessData with
            | intro firstWitness secondWitness =>
                exact
                  CompactNetWitness_prefixed_composite_closed prefixCarrier firstWitness
                    secondWitness compositeRel

end BEDC.Derived.CompactUp
