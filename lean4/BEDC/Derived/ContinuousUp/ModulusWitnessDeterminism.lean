import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousModulusWitness_modulus_hsame_deterministic
    {source source' modulus modulus' target target' : BHist} :
    hsame source source' → hsame target target' →
      ContinuousModulusWitness source modulus target →
        ContinuousModulusWitness source' modulus' target' → hsame modulus modulus' := by
  intro sameSource sameTarget left right
  cases sameSource
  cases sameTarget
  cases left with
  | intro _sourceCarrier leftRest =>
      cases leftRest with
      | intro _modulusCarrier leftRest =>
          cases leftRest with
          | intro _targetCarrier leftRel =>
              cases right with
              | intro _sourceCarrier' rightRest =>
                  cases rightRest with
                  | intro _modulusCarrier' rightRest =>
                      cases rightRest with
                      | intro _targetCarrier' rightRel =>
                          exact cont_left_cancel leftRel rightRel

theorem ContinuousModulusWitness_target_hsame_deterministic
    {source source' modulus target target' : BHist} :
    hsame source source' →
      ContinuousModulusWitness source modulus target →
        ContinuousModulusWitness source' modulus target' → hsame target target' := by
  intro sameSource left right
  cases sameSource
  cases left with
  | intro _sourceCarrier leftRest =>
      cases leftRest with
      | intro _modulusCarrier leftRest =>
          cases leftRest with
          | intro _targetCarrier leftRel =>
              cases right with
              | intro _sourceCarrier' rightRest =>
                  cases rightRest with
                  | intro _modulusCarrier' rightRest =>
                      cases rightRest with
                      | intro _targetCarrier' rightRel =>
                          exact cont_deterministic leftRel rightRel

theorem ContinuousModulusWitness_source_hsame_deterministic
    {source source' modulus target target' : BHist} :
    hsame target target' →
      ContinuousModulusWitness source modulus target →
        ContinuousModulusWitness source' modulus target' → hsame source source' := by
  intro sameTarget left right
  cases sameTarget
  cases left with
  | intro _sourceCarrier leftRest =>
      cases leftRest with
      | intro _modulusCarrier leftRest =>
          cases leftRest with
          | intro _targetCarrier leftRel =>
              cases right with
              | intro _sourceCarrier' rightRest =>
                  cases rightRest with
                  | intro _modulusCarrier' rightRest =>
                      cases rightRest with
                      | intro _targetCarrier' rightRel =>
                          exact cont_right_cancel leftRel rightRel

theorem ContinuousModulusChain_second_deterministic
    {source first second second' target : BHist} :
    ContinuousModulusChain source first second target →
      ContinuousModulusChain source first second' target → hsame second second' := by
  intro left right
  cases left with
  | intro _sourceCarrier leftRest =>
      cases leftRest with
      | intro _firstCarrier leftRest =>
          cases leftRest with
          | intro _secondCarrier leftRest =>
              cases leftRest with
              | intro _targetCarrier leftWitness =>
                  cases leftWitness with
                  | intro middle leftMiddle =>
                      cases leftMiddle with
                      | intro firstRel secondRel =>
                          cases right with
                          | intro _sourceCarrier' rightRest =>
                              cases rightRest with
                              | intro _firstCarrier' rightRest =>
                                  cases rightRest with
                                  | intro _secondCarrier' rightRest =>
                                      cases rightRest with
                                      | intro _targetCarrier' rightWitness =>
                                          cases rightWitness with
                                          | intro middle' rightMiddle =>
                                              cases rightMiddle with
                                              | intro firstRel' secondRel' =>
                                                  have sameMiddle : hsame middle middle' :=
                                                    cont_deterministic firstRel firstRel'
                                                  cases sameMiddle
                                                  exact cont_left_cancel secondRel secondRel'

theorem ContinuousFunctionCarrier_map_deterministic
    {source map map' target modulus cert : BHist} :
    ContinuousFunctionCarrier source map target modulus cert →
      ContinuousFunctionCarrier source map' target modulus cert → hsame map map' := by
  intro left right
  cases left with
  | intro _sourceCarrier leftRest =>
      cases leftRest with
      | intro _targetCarrier leftRest =>
          cases leftRest with
          | intro _mapCarrier leftRest =>
              cases leftRest with
              | intro _modulusCarrier leftRest =>
                  cases leftRest with
                  | intro sourceMap _targetCert =>
                      cases right with
                      | intro _sourceCarrier' rightRest =>
                          cases rightRest with
                          | intro _targetCarrier' rightRest =>
                              cases rightRest with
                              | intro _mapCarrier' rightRest =>
                                  cases rightRest with
                                  | intro _modulusCarrier' rightRest =>
                                      cases rightRest with
                                      | intro sourceMap' _targetCert' =>
                                          exact cont_left_cancel sourceMap sourceMap'

theorem ContinuousFunctionCarrier_source_deterministic
    {source source' map target modulus cert : BHist} :
    ContinuousFunctionCarrier source map target modulus cert →
      ContinuousFunctionCarrier source' map target modulus cert → hsame source source' := by
  intro left right
  cases left with
  | intro _sourceCarrier leftRest =>
      cases leftRest with
      | intro _targetCarrier leftRest =>
          cases leftRest with
          | intro _mapCarrier leftRest =>
              cases leftRest with
              | intro _modulusCarrier leftRest =>
                  cases leftRest with
                  | intro sourceMap _targetCert =>
                      cases right with
                      | intro _sourceCarrier' rightRest =>
                          cases rightRest with
                          | intro _targetCarrier' rightRest =>
                              cases rightRest with
                              | intro _mapCarrier' rightRest =>
                                  cases rightRest with
                                  | intro _modulusCarrier' rightRest =>
                                      cases rightRest with
                                      | intro sourceMap' _targetCert' =>
                                          exact cont_right_cancel sourceMap sourceMap'

theorem ContinuousFunctionCarrier_comp_public_readback
    {source middle target target' f g fg modF modG modFG certF certG cert cert' : BHist} :
    ContinuousFunctionCarrier source f middle modF certF ->
      ContinuousFunctionCarrier middle g target modG certG ->
        Cont f g fg -> Cont modF modG modFG -> Cont target modFG cert ->
          ContinuousFunctionCarrier source fg target' modFG cert' ->
            hsame target target' ∧ hsame cert cert' := by
  intro first second fgRel modRel certRel displayed
  exact
    ContinuousFunctionCarrier_target_cert_deterministic
      (ContinuousFunctionCarrier_comp_closed first second fgRel modRel certRel) displayed

theorem ContinuousModulusWitness_prefixed_composite_middle_deterministic_factorization
    {p source first second composite target : BHist} :
    UnaryHistory first -> UnaryHistory second -> Cont first second composite ->
      ContinuousModulusWitness (append p source) composite (append p target) ->
        ∃ middle : BHist,
          ContinuousModulusWitness source first middle ∧
            ContinuousModulusWitness middle second target ∧
              (∀ {middle' : BHist}, ContinuousModulusWitness source first middle' ->
                ContinuousModulusWitness middle' second target -> hsame middle middle') := by
  intro firstCarrier secondCarrier compositeRel prefixedWitness
  have factorized :=
    ContinuousModulusWitness_prefixed_composite_factorizes
      firstCarrier secondCarrier compositeRel prefixedWitness
  cases factorized with
  | intro middle data =>
      cases data with
      | intro firstWitness secondWitness =>
          exact Exists.intro middle
            (And.intro firstWitness
              (And.intro secondWitness
                (by
                  intro middle' firstWitness' _secondWitness'
                  exact ContinuousModulusWitness_target_hsame_deterministic
                    (hsame_refl source) firstWitness firstWitness')))

theorem ContinuousModulusWitness_prefixed_composite_first_deterministic
    {p source first first' second composite composite' target : BHist} :
    UnaryHistory first -> UnaryHistory first' -> UnaryHistory second ->
      Cont first second composite -> Cont first' second composite' ->
        ContinuousModulusWitness (append p source) composite (append p target) ->
          ContinuousModulusWitness (append p source) composite' (append p target) ->
            hsame first first' := by
  intro firstCarrier first'Carrier secondCarrier compositeRel composite'Rel leftPrefixed
    rightPrefixed
  have leftFactorized :=
    ContinuousModulusWitness_prefixed_composite_factorizes
      firstCarrier secondCarrier compositeRel leftPrefixed
  have rightFactorized :=
    ContinuousModulusWitness_prefixed_composite_factorizes
      first'Carrier secondCarrier composite'Rel rightPrefixed
  cases leftFactorized with
  | intro middle leftData =>
      cases leftData with
      | intro leftFirst leftSecond =>
          cases rightFactorized with
          | intro middle' rightData =>
              cases rightData with
              | intro rightFirst rightSecond =>
                  have sameMiddle : hsame middle middle' :=
                    ContinuousModulusWitness_source_hsame_deterministic
                      (hsame_refl target) leftSecond rightSecond
                  exact ContinuousModulusWitness_modulus_hsame_deterministic
                    (hsame_refl source) sameMiddle leftFirst rightFirst

theorem ContinuousModulusWitness_prefixed_composite_source_deterministic
    {p source source' first second composite target : BHist} :
    UnaryHistory first -> UnaryHistory second -> Cont first second composite ->
      ContinuousModulusWitness (append p source) composite (append p target) ->
        ContinuousModulusWitness (append p source') composite (append p target) ->
          hsame source source' := by
  intro firstCarrier secondCarrier compositeRel left right
  have leftFactor :=
    ContinuousModulusWitness_prefixed_composite_factorizes firstCarrier secondCarrier compositeRel left
  have rightFactor :=
    ContinuousModulusWitness_prefixed_composite_factorizes firstCarrier secondCarrier compositeRel right
  cases leftFactor with
  | intro middle leftData =>
      cases rightFactor with
      | intro middle' rightData =>
          have sameMiddle : hsame middle middle' :=
            ContinuousModulusWitness_source_hsame_deterministic (hsame_refl target)
              leftData.right rightData.right
          exact
            ContinuousModulusWitness_source_hsame_deterministic sameMiddle leftData.left
              rightData.left

theorem ContinuousModulusWitness_prefixed_composite_second_deterministic
    {p source first second second' composite composite' target : BHist} :
    UnaryHistory first -> UnaryHistory second -> UnaryHistory second' ->
      Cont first second composite -> Cont first second' composite' ->
        ContinuousModulusWitness (append p source) composite (append p target) ->
          ContinuousModulusWitness (append p source) composite' (append p target) ->
            hsame second second' := by
  intro firstCarrier secondCarrier second'Carrier compositeRel composite'Rel leftPrefixed
    rightPrefixed
  have leftFactorized :=
    ContinuousModulusWitness_prefixed_composite_factorizes
      firstCarrier secondCarrier compositeRel leftPrefixed
  have rightFactorized :=
    ContinuousModulusWitness_prefixed_composite_factorizes
      firstCarrier second'Carrier composite'Rel rightPrefixed
  cases leftFactorized with
  | intro middle leftData =>
      cases leftData with
      | intro leftFirst leftSecond =>
          cases rightFactorized with
          | intro middle' rightData =>
              cases rightData with
              | intro rightFirst rightSecond =>
                  have sameMiddle : hsame middle middle' :=
                    ContinuousModulusWitness_target_hsame_deterministic
                      (hsame_refl source) leftFirst rightFirst
                  exact ContinuousModulusWitness_modulus_hsame_deterministic
                    sameMiddle (hsame_refl target) leftSecond rightSecond

theorem ContinuousFunctionCarrier_prefixed_graph_chain_second_deterministic
    {p source map target delta1 delta2 delta2' delta delta' cert : BHist} :
    UnaryHistory delta1 → UnaryHistory delta2 → UnaryHistory delta2' →
      Cont delta1 delta2 delta → Cont delta1 delta2' delta' →
        ContinuousFunctionCarrier (append p source) map (append p target) delta
            (append p cert) →
          ContinuousFunctionCarrier (append p source) map (append p target) delta'
              (append p cert) →
            hsame delta2 delta2' := by
  intro _delta1Carrier _delta2Carrier _delta2'Carrier leftComposite rightComposite left right
  cases left with
  | intro _leftSource leftRest =>
      cases leftRest with
      | intro _leftTarget leftRest =>
          cases leftRest with
          | intro _leftMap leftRest =>
              cases leftRest with
              | intro _leftDelta leftRest =>
                  cases leftRest with
                  | intro _leftGraph leftCert =>
                      cases right with
                      | intro _rightSource rightRest =>
                          cases rightRest with
                          | intro _rightTarget rightRest =>
                              cases rightRest with
                              | intro _rightMap rightRest =>
                                  cases rightRest with
                                  | intro _rightDelta rightRest =>
                                      cases rightRest with
                                      | intro _rightGraph rightCert =>
                                          have sameDelta : hsame delta delta' :=
                                            cont_left_cancel leftCert rightCert
                                          cases sameDelta
                                          exact cont_left_cancel leftComposite rightComposite

theorem ContinuousFunctionCarrier_prefixed_graph_chain_public_readback
    {p source map target target' delta1 delta2 delta cert cert' : BHist} :
    UnaryHistory p -> UnaryHistory source -> UnaryHistory target -> UnaryHistory map ->
      Cont source map target -> ContinuousModulusChain target delta1 delta2 cert ->
        Cont delta1 delta2 delta ->
          ContinuousFunctionCarrier (append p source) map (append p target') delta
              (append p cert') ->
            hsame target target' /\ hsame cert cert' := by
  intro prefixCarrier sourceCarrier targetCarrier mapCarrier graphRel chain compositeRel
    displayed
  have canonical :
      ContinuousFunctionCarrier (append p source) map (append p target) delta
        (append p cert) :=
    ContinuousFunctionCarrier_prefixed_graph_chain_closed prefixCarrier sourceCarrier targetCarrier
      mapCarrier graphRel chain compositeRel
  have readback :
      hsame (append p target) (append p target') ∧ hsame (append p cert) (append p cert') :=
    ContinuousFunctionCarrier_target_cert_deterministic canonical displayed
  exact
    And.intro
      (append_left_cancel (h := p) readback.left)
      (append_left_cancel (h := p) readback.right)

end BEDC.Derived.ContinuousUp
