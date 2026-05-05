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

end BEDC.Derived.ConvexSetUp
