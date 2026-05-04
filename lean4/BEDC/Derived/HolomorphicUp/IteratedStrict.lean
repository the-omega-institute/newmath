import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

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

end BEDC.Derived.HolomorphicUp
