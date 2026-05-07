import BEDC.Derived.HilbertUp
import BEDC.Derived.RandomVarUp
import BEDC.Derived.VecSpaceUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units

namespace BEDC.Derived.CondExpUp

open BEDC.Derived.HilbertUp
open BEDC.Derived.RandomVarUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem CondExpCarrier_obligation {targetTotal sourceTotal preX x p residual : BHist} :
    RandomVarTotalReadbackCertificate targetTotal sourceTotal preX ->
      HilbertSingletonProjectionWitness x p ->
        Cont p residual x ->
          hsame preX sourceTotal ∧ VecSpaceSingletonCarrier x ∧ VecSpaceSingletonCarrier p ∧
            VecSpaceSingletonCarrier residual ∧ hsame residual BHist.Empty ∧ Cont p residual x := by
  intro readback projection residualRow
  have preXSource : hsame preX sourceTotal :=
    cont_deterministic readback.chosen_readback readback.carried_total_bridge
  have xCarrier : VecSpaceSingletonCarrier x := projection.left
  have pCarrier : VecSpaceSingletonCarrier p := projection.right.left
  have residualEmpty : hsame residual BHist.Empty :=
    cont_right_unit_unique
      (cont_hsame_transport pCarrier (hsame_refl residual) xCarrier residualRow)
  exact And.intro preXSource
    (And.intro xCarrier
      (And.intro pCarrier
        (And.intro residualEmpty (And.intro residualEmpty residualRow))))

end BEDC.Derived.CondExpUp
