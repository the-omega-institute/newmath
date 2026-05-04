import BEDC.Derived.HolomorphicUp.IteratedTransport

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem IteratedCplxDiff_add_closed_unary_readback {seed middle target : BHist}
    {n m : Nat} :
    IteratedCplxDiff seed n middle -> IteratedCplxDiff middle m target ->
      IteratedCplxDiff seed (n + m) target ∧ (UnaryHistory seed -> UnaryHistory target) := by
  intro left right
  induction m generalizing target with
  | zero =>
      exact IteratedCplxDiff_hsame_transport_unary_readback (hsame_refl seed) right left
  | succ m ih =>
      cases right with
      | intro previous rest =>
          cases rest with
          | intro step data =>
              have prefixClosed := ih data.left
              exact
                And.intro
                  (Exists.intro previous
                    (Exists.intro step
                      (And.intro prefixClosed.left
                        (And.intro data.right.left data.right.right))))
                  (fun seedUnary =>
                    unary_cont_closed (prefixClosed.right seedUnary) data.right.left
                      data.right.right)

end BEDC.Derived.HolomorphicUp
