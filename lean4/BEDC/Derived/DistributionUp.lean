import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.Derived.RandomVarUp

namespace BEDC.Derived.DistributionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RandomVarUp

theorem DistributionPushforwardWitness_total_mass_unit
    {targetTotal sourceTotal chosenPreimage sourceTotalMass pushedTotal probabilityUnit : BHist} :
    RandomVarTotalReadbackCertificate targetTotal sourceTotal chosenPreimage ->
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

theorem DistributionPushforward_relative_difference_additivity
    {sourceB sourceD sourceA pushB pushD pushA pushSum : BHist} :
    Cont sourceB sourceD sourceA -> hsame pushA sourceA -> hsame pushB sourceB ->
      hsame pushD sourceD -> Cont pushB pushD pushSum -> hsame pushA pushSum := by
  intro sourceSum pushAClass pushBClass pushDClass pushSumCont
  have sourcePushSum : hsame sourceA pushSum :=
    cont_respects_hsame (hsame_symm pushBClass) (hsame_symm pushDClass) sourceSum pushSumCont
  exact hsame_trans pushAClass sourcePushSum

end BEDC.Derived.DistributionUp
