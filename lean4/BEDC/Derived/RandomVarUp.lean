import BEDC.FKernel.Unary
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Bundle

namespace BEDC.Derived.RandomVarUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.Bundle

def RandomVarTotalDefectEvent (sourceTotal chosenPreimage defect : BHist) : Prop :=
  Cont chosenPreimage defect sourceTotal

theorem RandomVarTotalPreimage_composition_exactness
    {sourceTotal middleTotal targetTotal middlePreimage compositePreimage : BHist} :
    UnaryHistory sourceTotal -> UnaryHistory middleTotal -> hsame targetTotal BHist.Empty ->
      hsame middleTotal BHist.Empty -> Cont middleTotal targetTotal middlePreimage ->
        Cont sourceTotal middlePreimage compositePreimage ->
          UnaryHistory compositePreimage ∧ hsame compositePreimage sourceTotal := by
  intro sourceUnary _middleUnary targetEmpty middleEmpty middleReadback compositeReadback
  have middleTargetEmpty : Cont middleTotal BHist.Empty middlePreimage :=
    cont_hsame_transport (hsame_refl middleTotal) targetEmpty (hsame_refl middlePreimage)
      middleReadback
  have middlePreimageSame : hsame middlePreimage middleTotal :=
    cont_right_unit_result middleTargetEmpty
  have middlePreimageEmpty : hsame middlePreimage BHist.Empty :=
    hsame_trans middlePreimageSame middleEmpty
  have compositeRightUnit : Cont sourceTotal BHist.Empty compositePreimage :=
    cont_hsame_transport (hsame_refl sourceTotal) middlePreimageEmpty
      (hsame_refl compositePreimage) compositeReadback
  have compositeSame : hsame compositePreimage sourceTotal :=
    cont_right_unit_result compositeRightUnit
  exact And.intro (unary_transport sourceUnary (hsame_symm compositeSame)) compositeSame

structure RandomVarTotalReadbackCertificate
    (targetTotal sourceTotal chosenPreimage : BHist) : Prop where
  chosen_readback : Cont targetTotal BHist.Empty chosenPreimage
  carried_total_bridge : Cont targetTotal BHist.Empty sourceTotal

theorem RandomVarTotalReadbackCertificate_total_event_preimage_exactness
    {targetTotal sourceTotal chosenPreimage : BHist} :
    UnaryHistory sourceTotal ->
      RandomVarTotalReadbackCertificate targetTotal sourceTotal chosenPreimage ->
        UnaryHistory chosenPreimage ∧ hsame chosenPreimage sourceTotal := by
  intro sourceUnary cert
  have chosenSource : hsame chosenPreimage sourceTotal :=
    cont_deterministic cert.chosen_readback cert.carried_total_bridge
  exact And.intro (unary_transport sourceUnary (hsame_symm chosenSource)) chosenSource

theorem RandomVarTotalReadbackCertificate_source_coverage
    {targetTotal sourceTotal chosenPreimage sourcePoint gap : BHist} :
    RandomVarTotalReadbackCertificate targetTotal sourceTotal chosenPreimage ->
      Cont sourcePoint gap sourceTotal -> Cont sourcePoint gap chosenPreimage := by
  intro cert sourceCoverage
  have chosenSource : hsame chosenPreimage sourceTotal :=
    cont_deterministic cert.chosen_readback cert.carried_total_bridge
  exact cont_result_hsame_transport sourceCoverage (hsame_symm chosenSource)

theorem RandomVarTotalReadbackCertificate_composition_total_event_preimage_exactness
    {omegaU omegaT omegaS preY preX preYX : BHist} :
    RandomVarTotalReadbackCertificate omegaU omegaT preY ->
      RandomVarTotalReadbackCertificate omegaT omegaS preX ->
        Cont preY BHist.Empty preYX ->
          hsame preYX omegaS ∧ hsame preYX preY ∧ hsame preY omegaT ∧ hsame preX omegaS := by
  intro upperCert lowerCert compositeReadback
  have compositeChosen : hsame preYX preY :=
    cont_deterministic compositeReadback (cont_right_unit preY)
  have upperChosenTarget : hsame preY omegaT :=
    cont_deterministic upperCert.chosen_readback upperCert.carried_total_bridge
  have lowerTargetSource : hsame omegaT omegaS :=
    cont_deterministic (cont_right_unit omegaT) lowerCert.carried_total_bridge
  have lowerChosenSource : hsame preX omegaS :=
    cont_deterministic lowerCert.chosen_readback lowerCert.carried_total_bridge
  exact And.intro (hsame_trans compositeChosen (hsame_trans upperChosenTarget lowerTargetSource))
    (And.intro compositeChosen (And.intro upperChosenTarget lowerChosenSource))

theorem RandomVarTotalReadbackCertificate_carried_bridge_chosen_preimage_exactness_iff
    {targetTotal sourceTotal chosenPreimage : BHist} :
    Cont targetTotal BHist.Empty chosenPreimage ->
      (Cont targetTotal BHist.Empty sourceTotal ↔ hsame chosenPreimage sourceTotal) := by
  intro chosenReadback
  constructor
  · intro carriedBridge
    exact cont_deterministic chosenReadback carriedBridge
  · intro chosenExact
    exact cont_result_hsame_transport chosenReadback chosenExact

theorem RandomVarTotalDefectEvent_vanishing_total_exactness_iff
    {sourceTotal chosenPreimage defect : BHist} :
    RandomVarTotalDefectEvent sourceTotal chosenPreimage defect ->
      (hsame chosenPreimage sourceTotal ↔ hsame defect BHist.Empty) := by
  intro defectEvent
  constructor
  · intro chosenExact
    have transportedEvent : Cont sourceTotal defect sourceTotal :=
      cont_hsame_transport chosenExact (hsame_refl defect) (hsame_refl sourceTotal) defectEvent
    exact cont_right_unit_unique transportedEvent
  · intro defectEmpty
    have rightUnitEvent : Cont chosenPreimage BHist.Empty sourceTotal :=
      cont_hsame_transport (hsame_refl chosenPreimage) defectEmpty (hsame_refl sourceTotal)
        defectEvent
    exact hsame_symm (cont_right_unit_result rightUnitEvent)

theorem RandomVarTotalReadbackCertificate_total_target_reflection_criterion
    {targetTotal sourceTotal chosenPreimage targetEvent eventPreimage : BHist} :
    RandomVarTotalReadbackCertificate targetTotal sourceTotal chosenPreimage ->
      Cont targetEvent BHist.Empty eventPreimage ->
        hsame targetEvent targetTotal -> hsame eventPreimage sourceTotal := by
  intro readbackCert eventReadback eventTarget
  have targetReadback : Cont targetTotal BHist.Empty eventPreimage :=
    cont_hsame_transport eventTarget (hsame_refl BHist.Empty) (hsame_refl eventPreimage)
      eventReadback
  exact cont_deterministic targetReadback readbackCert.carried_total_bridge

theorem RandomVarPreimage_disjoint_binary_union_exactness
    {B C U_T A_B A_C A_U U_S : BHist} :
    hsame A_B B -> hsame A_C C -> hsame A_U U_T -> Cont B C U_T ->
      Cont A_B A_C U_S -> (hsame B C -> False) ->
        hsame A_U U_S ∧ (hsame A_B A_C -> False) := by
  intro samePreimageB samePreimageC samePreimageUnion targetUnion sourceUnion targetDisjoint
  have transportedUnion : hsame U_T U_S :=
    cont_respects_hsame (hsame_symm samePreimageB) (hsame_symm samePreimageC)
      targetUnion sourceUnion
  have sourceDisjoint : hsame A_B A_C -> False := by
    intro sameSource
    exact targetDisjoint
      (hsame_trans (hsame_symm samePreimageB) (hsame_trans sameSource samePreimageC))
  exact And.intro (hsame_trans samePreimageUnion transportedUnion) sourceDisjoint

theorem RandomVarPreimage_relative_difference_exactness
    {A B D_T A_S B_S D_X D_S : BHist} :
    hsame A_S A -> hsame B_S B -> hsame D_X D_T -> Cont B D_T A ->
      Cont B_S D_S A_S -> hsame D_X D_S := by
  intro sameSourceEndpoint sameSourceBase sameDiffTarget targetDifference sourceDifference
  have sourceAtTarget : Cont B D_S A :=
    cont_hsame_transport sameSourceBase (hsame_refl D_S) sameSourceEndpoint sourceDifference
  have targetDiffSourceDiff : hsame D_T D_S :=
    cont_left_cancel targetDifference sourceAtTarget
  exact hsame_trans sameDiffTarget targetDiffSourceDiff

theorem RandomVarPreimage_complement_difference_exactness
    {omegaT omegaS preOmega B BTComp BS BComp preComp : BHist} :
    RandomVarTotalReadbackCertificate omegaT omegaS preOmega -> hsame BS B ->
      hsame preComp BTComp -> Cont B BTComp omegaT -> Cont BS BComp omegaS ->
        hsame preComp BComp ∧ hsame preOmega omegaS := by
  intro cert sameBase samePreComp targetComplement sourceComplement
  have sameTotals : hsame omegaT omegaS :=
    cont_deterministic (cont_right_unit omegaT) cert.carried_total_bridge
  have targetComplementAtSourceTotal : Cont B BTComp omegaS :=
    cont_result_hsame_transport targetComplement sameTotals
  have sourceComplementAtTargetBase : Cont B BComp omegaS :=
    cont_hsame_transport sameBase (hsame_refl BComp) (hsame_refl omegaS) sourceComplement
  have sameTargetSourceComp : hsame BTComp BComp :=
    cont_left_cancel targetComplementAtSourceTotal sourceComplementAtTargetBase
  have samePreOmegaSource : hsame preOmega omegaS :=
    cont_deterministic cert.chosen_readback cert.carried_total_bridge
  exact And.intro (hsame_trans samePreComp sameTargetSourceComp) samePreOmegaSource

theorem RandomVarTotalReadbackCertificate_terminal_readback_uniqueness
    {targetTotal sourceTotal chosenPreimage alternatePreimage : BHist} :
    RandomVarTotalReadbackCertificate targetTotal sourceTotal chosenPreimage ->
      Cont targetTotal BHist.Empty alternatePreimage ->
        hsame alternatePreimage sourceTotal ∧ hsame alternatePreimage chosenPreimage := by
  intro cert alternateReadback
  have sameAlternateSource : hsame alternatePreimage sourceTotal :=
    cont_deterministic alternateReadback cert.carried_total_bridge
  have sameAlternateChosen : hsame alternatePreimage chosenPreimage :=
    cont_deterministic alternateReadback cert.chosen_readback
  exact And.intro sameAlternateSource sameAlternateChosen

theorem RandomVarTotalReadbackCertificate_minimal_obstruction
    {targetTotal sourceTotal chosenPreimage : BHist} :
    RandomVarTotalReadbackCertificate targetTotal sourceTotal chosenPreimage ->
      (UnaryHistory sourceTotal ->
          UnaryHistory chosenPreimage ∧ hsame chosenPreimage sourceTotal) ∧
        ((hsame chosenPreimage sourceTotal -> False) ->
          RandomVarTotalReadbackCertificate targetTotal sourceTotal chosenPreimage -> False) := by
  intro cert
  constructor
  · intro sourceUnary
    exact RandomVarTotalReadbackCertificate_total_event_preimage_exactness sourceUnary cert
  · intro obstruction certAgain
    exact obstruction (cont_deterministic certAgain.chosen_readback certAgain.carried_total_bridge)

theorem RandomVarPreimage_empty_event_exactness
    {targetEmpty sourceEmpty preimage : BHist} :
    hsame targetEmpty BHist.Empty -> hsame sourceEmpty BHist.Empty ->
      Cont targetEmpty BHist.Empty preimage -> hsame preimage sourceEmpty := by
  intro targetEmptyZero sourceEmptyZero preimageReadback
  have preimageTarget : hsame preimage targetEmpty :=
    cont_right_unit_result preimageReadback
  exact hsame_trans preimageTarget (hsame_trans targetEmptyZero (hsame_symm sourceEmptyZero))

def RandomVarPreimageUnionFold : ProbeBundle BHist -> BHist
  | ProbeBundle.Bnil => BHist.Empty
  | ProbeBundle.Bcons x xs => append x (RandomVarPreimageUnionFold xs)

theorem RandomVarPreimage_countable_union_exactness
    (left right : ProbeBundle BHist) :
    hsame (RandomVarPreimageUnionFold (bundleAppend left right))
      (append (RandomVarPreimageUnionFold left) (RandomVarPreimageUnionFold right)) := by
  induction left with
  | Bnil =>
      exact (append_empty_left (RandomVarPreimageUnionFold right)).symm
  | Bcons x xs ih =>
      exact (congrArg (append x) ih).trans
        (append_assoc x (RandomVarPreimageUnionFold xs)
          (RandomVarPreimageUnionFold right)).symm

end BEDC.Derived.RandomVarUp
