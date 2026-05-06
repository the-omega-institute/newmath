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

end BEDC.Derived.ProbSpaceUp
