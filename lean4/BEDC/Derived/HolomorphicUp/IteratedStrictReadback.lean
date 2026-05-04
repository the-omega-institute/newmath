import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem IteratedStrictCplxDiff_iteratedCplxDiff_unary_readback {seed h : BHist}
    {n : Nat} :
    IteratedStrictCplxDiff seed n h ->
      IteratedCplxDiff seed n h ∧ (UnaryHistory seed -> UnaryHistory h) := by
  intro diff
  induction n generalizing h with
  | zero =>
      exact And.intro diff (fun seedUnary => unary_transport seedUnary diff)
  | succ n ih =>
      cases diff with
      | intro previous rest =>
          cases rest with
          | intro step data =>
              have previousData := ih data.left
              exact
                And.intro
                  (Exists.intro previous
                    (Exists.intro step
                      (And.intro previousData.left
                        (And.intro data.right.left data.right.right.right))))
                  (fun seedUnary =>
                    unary_cont_closed (previousData.right seedUnary) data.right.left
                      data.right.right.right)

end BEDC.Derived.HolomorphicUp
