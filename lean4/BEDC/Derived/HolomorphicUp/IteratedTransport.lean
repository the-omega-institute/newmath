import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

theorem IteratedCplxDiff_hsame_transport_unary_readback {seed seed' h h' : BHist}
    {n : Nat} :
    hsame seed seed' -> hsame h h' -> IteratedCplxDiff seed n h ->
      IteratedCplxDiff seed' n h' ∧ (UnaryHistory seed' -> UnaryHistory h') := by
  intro sameSeed sameH diff
  have transported : IteratedCplxDiff seed' n h' := by
    induction n generalizing seed seed' h h' with
    | zero =>
        exact hsame_trans (hsame_symm sameSeed) (hsame_trans diff sameH)
    | succ n ih =>
        cases diff with
        | intro previous rest =>
            cases rest with
            | intro step data =>
                have previousTransported : IteratedCplxDiff seed' n previous :=
                  ih sameSeed (hsame_refl previous) data.left
                have stepTransported : Cont previous step h' :=
                  cont_hsame_transport (hsame_refl previous) (hsame_refl step) sameH
                    data.right.right
                exact
                  Exists.intro previous
                    (Exists.intro step
                      (And.intro previousTransported
                        (And.intro data.right.left stepTransported)))
  exact And.intro transported
    (fun seedUnary => IteratedCplxDiff_unary_of_seed seedUnary transported)

theorem IteratedStrictCplxDiff_hsame_transport_strict_prefix {seed seed' h h' : BHist}
    {n : Nat} :
    hsame seed seed' -> hsame h h' -> IteratedStrictCplxDiff seed (Nat.succ n) h ->
      IteratedStrictCplxDiff seed' (Nat.succ n) h' ∧
        (UnaryHistory seed' -> NatUnaryStrictPrefix seed' h') := by
  intro sameSeed sameH diff
  have transported : IteratedStrictCplxDiff seed' (Nat.succ n) h' := by
    induction n generalizing seed seed' h h' with
    | zero =>
        cases diff with
        | intro previous rest =>
            cases rest with
            | intro step data =>
                have previousTransported : IteratedStrictCplxDiff seed' Nat.zero previous :=
                  hsame_trans (hsame_symm sameSeed) data.left
                have stepTransported : Cont previous step h' :=
                  cont_hsame_transport (hsame_refl previous) (hsame_refl step) sameH
                    data.right.right.right
                exact
                  Exists.intro previous
                    (Exists.intro step
                      (And.intro previousTransported
                        (And.intro data.right.left
                          (And.intro data.right.right.left stepTransported))))
    | succ n ih =>
        cases diff with
        | intro previous rest =>
            cases rest with
            | intro step data =>
                have previousTransported :
                    IteratedStrictCplxDiff seed' (Nat.succ n) previous :=
                  ih sameSeed (hsame_refl previous) data.left
                have stepTransported : Cont previous step h' :=
                  cont_hsame_transport (hsame_refl previous) (hsame_refl step) sameH
                    data.right.right.right
                exact
                  Exists.intro previous
                    (Exists.intro step
                      (And.intro previousTransported
                        (And.intro data.right.left
                          (And.intro data.right.right.left stepTransported))))
  exact And.intro transported
    (fun seedUnary => IteratedStrictCplxDiff_strict_prefix seedUnary transported)

end BEDC.Derived.HolomorphicUp
