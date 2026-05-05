import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

theorem IteratedStrictCplxDiff_unary_of_seed {seed h : BHist} {n : Nat} :
    UnaryHistory seed -> IteratedStrictCplxDiff seed n h -> UnaryHistory h := by
  intro seedUnary diff
  induction n generalizing h with
  | zero =>
      exact unary_transport seedUnary diff
  | succ n ih =>
      cases diff with
      | intro previous rest =>
          cases rest with
          | intro step data =>
              exact unary_cont_closed (ih data.left) data.right.left data.right.right.right

theorem IteratedStrictCplxDiff_forget_strict_unary_readback {seed h : BHist} {n : Nat} :
    IteratedStrictCplxDiff seed n h ->
      IteratedCplxDiff seed n h ∧ (UnaryHistory seed -> UnaryHistory h) := by
  intro diff
  have forgotten : IteratedCplxDiff seed n h := by
    induction n generalizing h with
    | zero =>
        exact diff
    | succ n ih =>
        cases diff with
        | intro previous rest =>
            cases rest with
            | intro step data =>
                exact
                  Exists.intro previous
                    (Exists.intro step
                      (And.intro (ih data.left)
                        (And.intro data.right.left data.right.right.right)))
  exact And.intro forgotten
    (fun seedUnary => IteratedCplxDiff_unary_of_seed seedUnary forgotten)

theorem IteratedStrictCplxDiff_endpoint_hsame_absurd {seed h : BHist} {n : Nat} :
    UnaryHistory seed -> IteratedStrictCplxDiff seed (Nat.succ n) h -> hsame seed h ->
      False := by
  intro seedUnary diff sameEndpoint
  have strictPrefix := IteratedStrictCplxDiff_strict_prefix seedUnary diff
  cases strictPrefix with
  | intro tail data =>
      exact
        NatUnaryStrictPrefix_tail_endpoint_hsame_absurd
          data.left data.right.left data.right.right sameEndpoint

theorem IteratedStrictCplxDiff_result_not_empty {seed h : BHist} {n : Nat} :
    IteratedStrictCplxDiff seed (Nat.succ n) h -> hsame h BHist.Empty -> False := by
  intro diff resultEmpty
  cases diff with
  | intro _previous rest =>
      cases rest with
      | intro step data =>
          have emptyStep :
              step = BHist.Empty :=
            (cont_empty_result_inversion
              (cont_result_hsame_transport data.right.right.right resultEmpty)).right
          exact data.right.right.left emptyStep

theorem IteratedStrictCplxDiff_zero_or_strict_prefix {seed h : BHist} {n : Nat} :
    UnaryHistory seed -> IteratedStrictCplxDiff seed n h ->
      hsame seed h ∨ NatUnaryStrictPrefix seed h := by
  intro seedUnary diff
  cases n with
  | zero =>
      exact Or.inl diff
  | succ n =>
      exact Or.inr (IteratedStrictCplxDiff_strict_prefix seedUnary diff)

end BEDC.Derived.HolomorphicUp
