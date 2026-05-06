import BEDC.FKernel.Unary
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Bundle
import BEDC.Derived.RandomVarUp
import BEDC.Derived.PreorderUp

namespace BEDC.Derived.DistributionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.Bundle
open BEDC.Derived.RandomVarUp
open BEDC.Derived.PreorderUp

theorem DistributionPushforward_total_mass_unit
    {sourceTotal targetTotal sourceMass pushedMass unitMass : BHist} :
    UnaryHistory sourceTotal -> UnaryHistory sourceMass ->
      Cont sourceTotal BHist.Empty targetTotal -> hsame sourceMass sourceTotal ->
        hsame pushedMass targetTotal -> hsame sourceMass unitMass ->
          UnaryHistory pushedMass ∧ hsame pushedMass unitMass := by
  intro _sourceTotalUnary sourceMassUnary totalReadback sourceMassTotal pushedMassTarget
  intro sourceMassUnit
  have targetSource : hsame targetTotal sourceTotal :=
    cont_right_unit_result totalReadback
  have pushedSource : hsame pushedMass sourceTotal :=
    hsame_trans pushedMassTarget targetSource
  have pushedSourceMass : hsame pushedMass sourceMass :=
    hsame_trans pushedSource (hsame_symm sourceMassTotal)
  have pushedUnit : hsame pushedMass unitMass :=
    hsame_trans pushedSourceMass sourceMassUnit
  exact And.intro (unary_transport sourceMassUnary (hsame_symm pushedSourceMass)) pushedUnit

theorem DistributionPushforwardWitness_total_mass_unit
    {targetTotal sourceTotal chosenPreimage sourceTotalMass pushedTotal probabilityUnit : BHist} :
    BEDC.Derived.RandomVarUp.RandomVarTotalReadbackCertificate targetTotal sourceTotal
      chosenPreimage ->
      Cont sourceTotal BHist.Empty sourceTotalMass ->
        hsame pushedTotal sourceTotalMass ->
          hsame sourceTotalMass probabilityUnit ->
            hsame pushedTotal probabilityUnit ∧ hsame chosenPreimage sourceTotal := by
  intro randomVarCert sourceTotalMassReadback pushedSourceMass sourceMassUnit
  have chosenSourceTotal : hsame chosenPreimage sourceTotal :=
    cont_deterministic randomVarCert.chosen_readback randomVarCert.carried_total_bridge
  have sourceMassSource : hsame sourceTotalMass sourceTotal :=
    cont_deterministic sourceTotalMassReadback (cont_right_unit sourceTotal)
  have chosenSourceMass : hsame chosenPreimage sourceTotalMass :=
    hsame_trans chosenSourceTotal (hsame_symm sourceMassSource)
  exact And.intro (hsame_trans pushedSourceMass sourceMassUnit)
    (hsame_trans chosenSourceMass sourceMassSource)

theorem DistributionPushforward_empty_target_event_zero_mass
    {targetEmpty sourceEmpty sourceValue pushValue : BHist} :
    hsame targetEmpty BHist.Empty -> hsame sourceEmpty BHist.Empty ->
      Cont sourceEmpty BHist.Empty sourceValue -> Cont targetEmpty sourceValue pushValue ->
        hsame pushValue BHist.Empty := by
  intro targetEmptyZero sourceEmptyZero sourceEndpoint pushEndpoint
  have sourceValueZero : hsame sourceValue BHist.Empty :=
    cont_respects_hsame sourceEmptyZero (hsame_refl BHist.Empty)
      sourceEndpoint (cont_left_unit BHist.Empty)
  have pushValueZero : hsame pushValue BHist.Empty :=
    cont_respects_hsame targetEmptyZero sourceValueZero pushEndpoint
      (cont_left_unit BHist.Empty)
  exact pushValueZero

theorem DistributionPushforward_finite_disjoint_union_additivity
    {sourceB sourceC sourceU pushedB pushedC pushedU pushedSum : BHist} :
    Cont sourceB sourceC sourceU -> hsame pushedU sourceU -> hsame pushedB sourceB ->
      hsame pushedC sourceC -> Cont pushedB pushedC pushedSum -> hsame pushedU pushedSum := by
  intro sourceUnion pushedUnionSource pushedBSource pushedCSource pushedUnion
  have sourcePushedUnion : hsame sourceU pushedSum :=
    cont_respects_hsame (hsame_symm pushedBSource) (hsame_symm pushedCSource)
      sourceUnion pushedUnion
  exact hsame_trans pushedUnionSource sourcePushedUnion

theorem DistributionPushforward_relative_difference_additivity
    {sourceB sourceD sourceA pushB pushD pushA pushSum : BHist} :
    Cont sourceB sourceD sourceA -> hsame pushA sourceA -> hsame pushB sourceB ->
      hsame pushD sourceD -> Cont pushB pushD pushSum -> hsame pushA pushSum := by
  intro sourceSum pushAClass pushBClass pushDClass pushSumCont
  have sourcePushSum : hsame sourceA pushSum :=
    cont_respects_hsame (hsame_symm pushBClass) (hsame_symm pushDClass) sourceSum pushSumCont
  exact hsame_trans pushAClass sourcePushSum

theorem DistributionPushforward_monotone_under_target_inclusion
    {sourceB sourceD sourceA pushB pushD pushA pushSum : BHist} :
    Cont sourceB sourceD sourceA -> hsame pushA sourceA -> hsame pushB sourceB ->
      hsame pushD sourceD -> Cont pushB pushD pushSum -> UnaryHistory pushD ->
        exists witness : BHist, Cont pushB witness pushA ∧ UnaryHistory witness := by
  intro sourceSum pushAClass pushBClass pushDClass pushSumCont pushDUnary
  have pushAFromSum : hsame pushA pushSum :=
    DistributionPushforward_relative_difference_additivity sourceSum pushAClass pushBClass
      pushDClass pushSumCont
  have pushDToPushA : Cont pushB pushD pushA :=
    cont_result_hsame_transport pushSumCont (hsame_symm pushAFromSum)
  exact Exists.intro pushD (And.intro pushDToPushA pushDUnary)

theorem DistributionPushforward_probability_bounds
    {event gap sourceTotal sourceTotalMass pushedEvent pushedTotal probabilityUnit pushedSum :
      BHist} :
    UnaryHistory event -> UnaryHistory gap -> Cont event gap sourceTotal ->
      Cont sourceTotal BHist.Empty sourceTotalMass -> hsame pushedEvent event ->
        hsame pushedTotal sourceTotalMass -> hsame sourceTotalMass probabilityUnit ->
          Cont pushedEvent gap pushedSum -> hsame pushedTotal pushedSum ->
            UnaryHistory pushedEvent ∧ PreorderPrefixLE pushedEvent probabilityUnit := by
  intro eventUnary gapUnary eventGap sourceMassReadback pushedEventEvent pushedTotalMass
  intro sourceMassUnit pushedSumCont pushedTotalSum
  have pushedEventUnary : UnaryHistory pushedEvent :=
    unary_transport eventUnary (hsame_symm pushedEventEvent)
  have sourceTotalUnary : UnaryHistory sourceTotal :=
    unary_cont_closed eventUnary gapUnary eventGap
  have sourceMassUnary : UnaryHistory sourceTotalMass :=
    unary_transport sourceTotalUnary (hsame_symm (cont_right_unit_result sourceMassReadback))
  have pushedTotalUnary : UnaryHistory pushedTotal :=
    unary_transport sourceMassUnary (hsame_symm pushedTotalMass)
  have pushedSumUnit : hsame pushedSum probabilityUnit :=
    hsame_trans (hsame_symm pushedTotalSum) (hsame_trans pushedTotalMass sourceMassUnit)
  have pushedSumUnitCont : Cont pushedEvent gap probabilityUnit :=
    cont_result_hsame_transport pushedSumCont pushedSumUnit
  exact And.intro pushedEventUnary
    (Exists.intro gap (And.intro gapUnary pushedSumUnitCont))

theorem DistributionPushforward_nonnegative_value_inheritance
    {sourceValue pushedValue witness : BHist} :
    UnaryHistory sourceValue -> Cont sourceValue BHist.Empty witness ->
      hsame pushedValue witness -> UnaryHistory pushedValue ∧ hsame pushedValue sourceValue := by
  intro sourceNonnegative sourceReadback pushedWitness
  have witnessSource : hsame witness sourceValue :=
    cont_right_unit_result sourceReadback
  have pushedSource : hsame pushedValue sourceValue :=
    hsame_trans pushedWitness witnessSource
  exact And.intro (unary_transport sourceNonnegative (hsame_symm pushedSource)) pushedSource

def DistributionPushforwardMassFold : ProbeBundle BHist -> BHist
  | ProbeBundle.Bnil => BHist.Empty
  | ProbeBundle.Bcons x xs => append x (DistributionPushforwardMassFold xs)

theorem DistributionPushforward_countable_disjoint_sigma_additivity
    (left right : ProbeBundle BHist) :
    hsame (DistributionPushforwardMassFold (bundleAppend left right))
      (append (DistributionPushforwardMassFold left) (DistributionPushforwardMassFold right)) := by
  induction left with
  | Bnil =>
      exact (append_empty_left (DistributionPushforwardMassFold right)).symm
  | Bcons x xs ih =>
      exact (congrArg (append x) ih).trans
        (append_assoc x (DistributionPushforwardMassFold xs)
          (DistributionPushforwardMassFold right)).symm

end BEDC.Derived.DistributionUp
