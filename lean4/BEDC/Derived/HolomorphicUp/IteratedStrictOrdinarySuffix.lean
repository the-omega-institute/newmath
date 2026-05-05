import BEDC.Derived.HolomorphicUp.IteratedComposition
import BEDC.Derived.PreorderUp

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PreorderUp

theorem IteratedStrictCplxDiff_ordinary_suffix_strict_prefix_readback
    {seed middle target : BHist} {n m : Nat} :
    IteratedStrictCplxDiff seed (Nat.succ n) middle ->
      IteratedCplxDiff middle m target ->
        IteratedCplxDiff seed (Nat.succ n + m) target ∧
          (UnaryHistory seed -> NatUnaryStrictPrefix seed target) := by
  intro left right
  have leftOrdinary : IteratedCplxDiff seed (Nat.succ n) middle :=
    (IteratedStrictCplxDiff_forget_strict_unary_readback left).left
  have joinedOrdinary : IteratedCplxDiff seed (Nat.succ n + m) target :=
    (IteratedCplxDiff_add_closed_unary_readback leftOrdinary right).left
  constructor
  · exact joinedOrdinary
  · intro seedUnary
    induction m generalizing target with
    | zero =>
        have strictMiddle : NatUnaryStrictPrefix seed middle :=
          IteratedStrictCplxDiff_strict_prefix seedUnary left
        cases strictMiddle with
        | intro tail data =>
            exact
              NatUnaryStrictPrefix_cont_hsame_transport data.left data.right.left
                data.right.right (hsame_refl seed) right
    | succ m ih =>
        cases right with
        | intro previous rest =>
            cases rest with
            | intro step data =>
                have previousOrdinary : IteratedCplxDiff seed (Nat.succ n + m) previous :=
                  (IteratedCplxDiff_add_closed_unary_readback leftOrdinary data.left).left
                have strictPrevious : NatUnaryStrictPrefix seed previous :=
                  ih data.left previousOrdinary
                have weakStep : PreorderPrefixLE previous target :=
                  Exists.intro step (And.intro data.right.left data.right.right)
                exact NatUnaryStrictPrefix_right_extension strictPrevious weakStep

end BEDC.Derived.HolomorphicUp
