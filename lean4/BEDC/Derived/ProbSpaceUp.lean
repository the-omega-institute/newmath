import BEDC.FKernel.Unary

namespace BEDC.Derived.ProbSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ProbSpaceComplementMass_additive_readback {omega one event complement sum : BHist} :
    UnaryHistory event -> UnaryHistory complement -> Cont event complement sum ->
      hsame omega sum -> hsame omega one -> hsame sum one ∧ UnaryHistory sum := by
  intro eventCarrier complementCarrier sumRel sameOmegaSum sameOmegaOne
  exact And.intro (hsame_trans (hsame_symm sameOmegaSum) sameOmegaOne)
    (unary_cont_closed eventCarrier complementCarrier sumRel)

theorem ProbSpaceComplementMass_right_solution
    {omega one event complement sum inverseEvent target : BHist} :
    UnaryHistory event -> UnaryHistory complement -> Cont event complement sum ->
      hsame omega sum -> hsame omega one -> Cont one inverseEvent target ->
        Cont event target one -> hsame complement target ∧ UnaryHistory target := by
  intro eventCarrier complementCarrier sumRel sameOmegaSum sameOmegaOne
  intro _inverseRel targetRel
  have sumOne : hsame sum one :=
    hsame_trans (hsame_symm sameOmegaSum) sameOmegaOne
  have eventComplementOne : Cont event complement one :=
    cont_result_hsame_transport sumRel sumOne
  have sameComplementTarget : hsame complement target :=
    cont_left_cancel eventComplementOne targetRel
  exact And.intro sameComplementTarget
    (unary_transport complementCarrier sameComplementTarget)

end BEDC.Derived.ProbSpaceUp
