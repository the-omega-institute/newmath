import BEDC.FKernel.Cont.Units
import BEDC.Derived.ConvexSetUp
import BEDC.Derived.PreorderUp

namespace BEDC.Derived.LPDualityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ConvexSetUp
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

theorem LPDualityFeasibleWeakDuality_prefix_order
    {primal left bridge right dual leftTail rightTail : BHist} :
    UnaryHistory leftTail -> Cont primal leftTail left -> hsame left bridge ->
      UnaryHistory rightTail -> Cont bridge rightTail right -> hsame right dual ->
        PreorderPrefixLE primal dual := by
  intro leftTailUnary primalLeft leftBridge rightTailUnary bridgeRight rightDual
  have primalLeftLE : PreorderPrefixLE primal left :=
    Exists.intro leftTail (And.intro leftTailUnary primalLeft)
  have leftBridgeLE : PreorderPrefixLE left bridge :=
    PreorderPrefixLE_of_hsame leftBridge
  have bridgeRightLE : PreorderPrefixLE bridge right :=
    Exists.intro rightTail (And.intro rightTailUnary bridgeRight)
  have rightDualLE : PreorderPrefixLE right dual :=
    PreorderPrefixLE_of_hsame rightDual
  exact PreorderPrefixLE_trans
    (PreorderPrefixLE_trans primalLeftLE leftBridgeLE)
    (PreorderPrefixLE_trans bridgeRightLE rightDualLE)

theorem LPDualityWeakDualityEquality_optimality
    {primal dual primalCompetitor dualCompetitor domain : BHist} :
    hsame primal dual -> PreorderPrefixLE primalCompetitor dual ->
      PreorderPrefixLE primal dualCompetitor -> PreorderPrefixLE primal domain ->
        PreorderPrefixLE primalCompetitor primal ∧ PreorderPrefixLE dual dualCompetitor ∧
          PreorderPrefixLE dual domain := by
  intro objectiveEquality competitorBound dualBound domainBound
  have dualPrimal : PreorderPrefixLE dual primal :=
    PreorderPrefixLE_of_hsame (hsame_symm objectiveEquality)
  exact And.intro
    (PreorderPrefixLE_trans competitorBound dualPrimal)
    (And.intro
      (PreorderPrefixLE_trans dualPrimal dualBound)
      (PreorderPrefixLE_trans dualPrimal domainBound))

theorem LPDualityComplementarySlackness_objective_equality
    {primal bridge dual primalCompetitor dualCompetitor domain : BHist} :
    Cont primal BHist.Empty bridge -> Cont bridge BHist.Empty dual ->
      PreorderPrefixLE primalCompetitor dual -> PreorderPrefixLE primal dualCompetitor ->
        PreorderPrefixLE primal domain ->
          hsame primal dual ∧ PreorderPrefixLE primalCompetitor primal ∧
            PreorderPrefixLE dual dualCompetitor ∧ PreorderPrefixLE dual domain := by
  intro primalBridge bridgeDual competitorBound dualBound domainBound
  have objective :
      hsame primal dual ∧ PreorderPrefixLE primal dual ∧ PreorderPrefixLE dual primal :=
    LPDualityComplementarySlackness_objective_hsame primalBridge bridgeDual
  have optimality :
      PreorderPrefixLE primalCompetitor primal ∧ PreorderPrefixLE dual dualCompetitor ∧
        PreorderPrefixLE dual domain :=
    LPDualityWeakDualityEquality_optimality
      objective.left competitorBound dualBound domainBound
  exact And.intro objective.left optimality

theorem LPDualityOptimalPrimalFace_binary_convex_closure
    {primal primal' mixture optimum : BHist} :
    hsame primal optimum -> hsame primal' optimum -> hsame optimum BHist.Empty ->
      Cont primal primal' mixture ->
        hsame mixture optimum ∧ PreorderPrefixLE mixture optimum ∧
          PreorderPrefixLE optimum mixture := by
  intro primalOpt primalOpt' optimumEmpty mixtureRow
  have primalEmpty : hsame primal BHist.Empty :=
    hsame_trans primalOpt optimumEmpty
  have primalEmpty' : hsame primal' BHist.Empty :=
    hsame_trans primalOpt' optimumEmpty
  have mixtureEmpty :
      ConvexSetSingletonAffineSpine [primal, primal'] mixture ∧
        hsame mixture BHist.Empty :=
    ConvexSetSingletonAffineSpine_midpoint_closure primalEmpty primalEmpty' mixtureRow
  have mixtureOpt : hsame mixture optimum :=
    hsame_trans mixtureEmpty.right (hsame_symm optimumEmpty)
  exact And.intro mixtureOpt
    (And.intro
      (PreorderPrefixLE_of_hsame mixtureOpt)
      (PreorderPrefixLE_of_hsame (hsame_symm mixtureOpt)))

end BEDC.Derived.LPDualityUp
