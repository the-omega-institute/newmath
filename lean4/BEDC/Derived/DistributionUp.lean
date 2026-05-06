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

end BEDC.Derived.DistributionUp
