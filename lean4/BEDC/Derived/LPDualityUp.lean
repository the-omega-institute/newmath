import BEDC.FKernel.Cont.Units
import BEDC.Derived.PreorderUp

namespace BEDC.Derived.LPDualityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.PreorderUp

theorem LPDualityComplementarySlackness_objective_hsame {primal bridge dual : BHist} :
    Cont primal BHist.Empty bridge -> Cont bridge BHist.Empty dual ->
      hsame primal dual ∧ PreorderPrefixLE primal dual ∧ PreorderPrefixLE dual primal := by
  intro primalBridge bridgeDual
  have samePrimalBridge : hsame bridge primal := cont_right_unit_result primalBridge
  have sameDualBridge : hsame dual bridge := cont_right_unit_result bridgeDual
  have samePrimalDual : hsame primal dual :=
    hsame_trans (hsame_symm samePrimalBridge) (hsame_symm sameDualBridge)
  exact And.intro samePrimalDual
    (And.intro
      (PreorderPrefixLE_of_hsame samePrimalDual)
      (PreorderPrefixLE_of_hsame (hsame_symm samePrimalDual)))

end BEDC.Derived.LPDualityUp
