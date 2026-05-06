import BEDC.FKernel.Cont

namespace BEDC.Derived.ConvexSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def ConvexSetSingletonAffineSpine : List BHist -> BHist -> Prop
  | [], z => hsame z BHist.Empty
  | x :: xs, z =>
      hsame x BHist.Empty ∧
        exists tail : BHist, ConvexSetSingletonAffineSpine xs tail ∧ Cont x tail z

theorem ConvexSetSingletonAffineSpine_closure {xs : List BHist} {z : BHist} :
    ConvexSetSingletonAffineSpine xs z -> hsame z BHist.Empty := by
  intro spine
  induction xs generalizing z with
  | nil =>
      exact spine
  | cons x xs ih =>
      cases spine with
      | intro xEmpty tailData =>
          cases tailData with
          | intro tail tailPack =>
              cases tailPack with
              | intro tailSpine continuation =>
                  have tailEmpty : hsame tail BHist.Empty := ih tailSpine
                  exact hsame_trans continuation (append_eq_empty_iff.mpr
                    (And.intro xEmpty tailEmpty))

theorem ConvexSetSingletonAffineSpine_midpoint_closure {x y endpoint : BHist} :
    hsame x BHist.Empty -> hsame y BHist.Empty -> Cont x y endpoint ->
      ConvexSetSingletonAffineSpine [x, y] endpoint ∧ hsame endpoint BHist.Empty := by
  intro xEmpty yEmpty endpointRow
  have tailSpine : ConvexSetSingletonAffineSpine [y] y :=
    And.intro yEmpty (Exists.intro BHist.Empty
      (And.intro (hsame_refl BHist.Empty) (cont_right_unit y)))
  have spine : ConvexSetSingletonAffineSpine [x, y] endpoint :=
    And.intro xEmpty (Exists.intro y (And.intro tailSpine endpointRow))
  exact And.intro spine (ConvexSetSingletonAffineSpine_closure spine)

end BEDC.Derived.ConvexSetUp
