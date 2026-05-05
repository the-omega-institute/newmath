import BEDC.Derived.HolomorphicUp.IteratedTransport
import BEDC.Derived.HolomorphicUp.IteratedStrict

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

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

theorem IteratedStrictCplxDiff_add_closed_strict_readback {seed middle target : BHist}
    {n m : Nat} :
    IteratedStrictCplxDiff seed n middle -> IteratedStrictCplxDiff middle m target ->
      IteratedStrictCplxDiff seed (n + m) target ∧
        (UnaryHistory seed -> UnaryHistory target) := by
  intro left right
  induction m generalizing target with
  | zero =>
      have transported : IteratedStrictCplxDiff seed (n + Nat.zero) target := by
        cases n with
        | zero =>
            exact hsame_trans left right
        | succ n =>
            exact
              (IteratedStrictCplxDiff_hsame_transport_strict_prefix
                (hsame_refl seed) right left).left
      exact And.intro transported
        (fun seedUnary =>
          unary_transport (IteratedStrictCplxDiff_unary_of_seed seedUnary left) right)
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
                        (And.intro data.right.left
                          (And.intro data.right.right.left data.right.right.right)))))
                  (fun seedUnary =>
                    unary_cont_closed (prefixClosed.right seedUnary) data.right.left
                      data.right.right.right)

theorem IteratedStrictCplxDiff_add_closed_strict_prefix_readback
    {seed middle target : BHist} {n m : Nat} :
    IteratedStrictCplxDiff seed n middle ->
      IteratedStrictCplxDiff middle (Nat.succ m) target ->
        IteratedStrictCplxDiff seed (n + Nat.succ m) target ∧
          (UnaryHistory seed -> NatUnaryStrictPrefix seed target) := by
  intro left right
  induction m generalizing target with
  | zero =>
      cases right with
      | intro previous rest =>
          cases rest with
          | intro step data =>
              have prefixTransported :
                  IteratedStrictCplxDiff seed n previous :=
                (IteratedStrictCplxDiff_hsame_transport_unary_readback
                  (hsame_refl seed) data.left left).left
              have joined :
                  IteratedStrictCplxDiff seed (n + Nat.succ Nat.zero) target :=
                Exists.intro previous
                  (Exists.intro step
                    (And.intro prefixTransported
                      (And.intro data.right.left
                        (And.intro data.right.right.left data.right.right.right))))
              exact And.intro joined
                (fun seedUnary => IteratedStrictCplxDiff_strict_prefix seedUnary joined)
  | succ m ih =>
      cases right with
      | intro previous rest =>
          cases rest with
          | intro step data =>
              have prefixClosed := ih data.left
              have joined :
                  IteratedStrictCplxDiff seed (n + Nat.succ (Nat.succ m)) target :=
                Exists.intro previous
                  (Exists.intro step
                    (And.intro prefixClosed.left
                      (And.intro data.right.left
                        (And.intro data.right.right.left data.right.right.right))))
              exact And.intro joined
                (fun seedUnary => IteratedStrictCplxDiff_strict_prefix seedUnary joined)

theorem IteratedStrictCplxDiff_add_closed_endpoint_hsame_absurd
    {seed middle target : BHist} {n m : Nat} :
    UnaryHistory seed -> IteratedStrictCplxDiff seed n middle ->
      IteratedStrictCplxDiff middle (Nat.succ m) target -> hsame seed target -> False := by
  intro seedUnary left right sameEndpoint
  have joined := IteratedStrictCplxDiff_add_closed_strict_prefix_readback left right
  have strictPrefix : NatUnaryStrictPrefix seed target := joined.right seedUnary
  cases strictPrefix with
  | intro tail data =>
      exact NatUnaryStrictPrefix_tail_endpoint_hsame_absurd
        data.left data.right.left data.right.right sameEndpoint

end BEDC.Derived.HolomorphicUp
