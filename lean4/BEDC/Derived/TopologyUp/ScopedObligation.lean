import BEDC.Derived.TopologyUp

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TopologyPublicOpenTree_constructor_exhaustion (T : BHistIndexedOpenCarrier)
    {i : T.OpenIx} {U : BHist -> Prop} :
    TopologyPublicOpenTree T i U ->
      (exists _carries : BHistCarriesOpen T i U, BHistGeneratedOpenExact T U) ∨
      (exists i0 : T.OpenIx, exists j0 : T.OpenIx, exists U0 : BHist -> Prop,
        exists V0 : BHist -> Prop,
          TopologyPublicOpenTree T i0 U0 ∧ TopologyPublicOpenTree T j0 V0 ∧
            (forall x : BHist, U x <-> (U0 x ∧ V0 x)) ∧ i = T.meet i0 j0) ∨
      (exists A : Type, exists idx : A -> T.OpenIx, exists Us : A -> BHist -> Prop,
        (forall a : A, TopologyPublicOpenTree T (idx a) (Us a)) ∧
          (forall {x : BHist}, UnaryHistory x ->
            (T.OpenAt i x <-> exists a : A, T.OpenAt (idx a) x)) ∧
            (forall x : BHist, U x <-> exists a : A, Us a x)) ∨
      (exists boundary : BHistIndexedBoundaryOpen T, i = boundary.bottom) ∨
      (exists boundary : BHistIndexedBoundaryOpen T, i = boundary.top) := by
  intro tree
  cases tree with
  | basic carries =>
      exact Or.inl (Exists.intro carries (Exists.intro i carries))
  | binaryMeet leftTree rightTree =>
      exact Or.inr (Or.inl
        (Exists.intro _
          (Exists.intro _
            (Exists.intro _
              (Exists.intro _
                (And.intro leftTree
                  (And.intro rightTree
                    (And.intro
                      (by
                        intro x
                        constructor
                        · intro both
                          exact both
                        · intro both
                          exact both)
                      rfl))))))))
  | arbitraryUnion children unionLaw =>
      exact Or.inr (Or.inr (Or.inl
        (Exists.intro _
          (Exists.intro _
            (Exists.intro _
              (And.intro children
                (And.intro unionLaw
                  (by
                    intro x
                    constructor
                    · intro witness
                      exact witness
                    · intro witness
                      exact witness))))))))
  | bottom boundary =>
      exact Or.inr (Or.inr (Or.inr (Or.inl (Exists.intro boundary rfl))))
  | top boundary =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Exists.intro boundary rfl))))

end BEDC.Derived.TopologyUp
