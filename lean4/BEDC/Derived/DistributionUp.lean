import BEDC.FKernel.Unary
import BEDC.FKernel.Cont.Units

namespace BEDC.Derived.DistributionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

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

end BEDC.Derived.DistributionUp
