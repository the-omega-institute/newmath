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

end BEDC.Derived.HolomorphicUp
