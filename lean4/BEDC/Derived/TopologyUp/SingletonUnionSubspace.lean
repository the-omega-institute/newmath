import BEDC.Derived.TopologyUp

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TopologySingleton_union_bottom_exactness {A : Type} (ι : A -> BHist)
    (allBottom : forall a : A, hsame (ι a) (BHist.e0 BHist.Empty)) :
    forall h : BHist,
      TopologySingletonOpenAt (BHist.e0 BHist.Empty) h <->
        exists a : A, TopologySingletonOpenAt (ι a) h := by
  intro h
  constructor
  · intro openBottom
    exact False.elim (not_hsame_e0_empty openBottom.left)
  · intro witness
    cases witness with
    | intro a openA =>
        have bottomAtA : hsame (BHist.e0 BHist.Empty) (ι a) :=
          hsame_symm (allBottom a)
        have openBottom : TopologySingletonOpenAt (BHist.e0 BHist.Empty) h :=
          And.intro (hsame_trans bottomAtA openA.left) openA.right
        exact False.elim (not_hsame_e0_empty openBottom.left)

theorem BHistSubspaceOpen_carrier_transport (T : BHistIndexedOpenCarrier)
    {S : BHist -> Prop} {i : T.OpenIx} {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> (S h ∧ S k ∧ hsame h k) ->
      ((S h ∧ T.OpenAt i h) <-> (S k ∧ T.OpenAt i k)) := by
  intro unaryH unaryK restrictedSame
  have stable : T.OpenAt i h <-> T.OpenAt i k :=
    T.membership_stable unaryH unaryK restrictedSame.right.right
  constructor
  · intro subH
    exact And.intro restrictedSame.right.left (Iff.mp stable subH.right)
  · intro subK
    exact And.intro restrictedSame.left (Iff.mpr stable subK.right)

theorem BHistSubspaceOpen_boundary_closure (T : BHistIndexedOpenCarrier)
    (boundary : BHistIndexedBoundaryOpen T) {S : BHist -> Prop} :
    (forall {h : BHist}, UnaryHistory h -> ((S h ∧ T.OpenAt boundary.bottom h) ↔ False)) ∧
      (forall {h : BHist}, UnaryHistory h -> ((S h ∧ T.OpenAt boundary.top h) ↔ S h)) := by
  constructor
  · intro h unaryH
    have bottomAt : T.OpenAt boundary.bottom h <-> False := boundary.bottom_law unaryH
    constructor
    · intro subBottom
      exact Iff.mp bottomAt subBottom.right
    · intro impossible
      exact False.elim impossible
  · intro h unaryH
    have topAt : T.OpenAt boundary.top h <-> True := boundary.top_law unaryH
    constructor
    · intro subTop
      exact subTop.left
    · intro inSubspace
      apply And.intro
      · exact inSubspace
      · apply Iff.mpr topAt
        constructor

theorem BHistSubspaceOpen_finite_intersection (T : BHistIndexedOpenCarrier)
    {S : BHist -> Prop} {i j : T.OpenIx} {h : BHist} :
    UnaryHistory h ->
      ((S h ∧ T.OpenAt (T.meet i j) h) <->
        ((S h ∧ T.OpenAt i h) ∧ (S h ∧ T.OpenAt j h))) := by
  intro unaryH
  have meetAt : T.OpenAt (T.meet i j) h <-> T.OpenAt i h ∧ T.OpenAt j h :=
    T.meet_law unaryH
  constructor
  · intro subMeet
    have openBoth : T.OpenAt i h ∧ T.OpenAt j h := Iff.mp meetAt subMeet.right
    exact And.intro
      (And.intro subMeet.left openBoth.left)
      (And.intro subMeet.left openBoth.right)
  · intro subBoth
    have openMeet : T.OpenAt (T.meet i j) h :=
      Iff.mpr meetAt (And.intro subBoth.left.right subBoth.right.right)
    exact And.intro subBoth.left.left openMeet

theorem BHistSubspaceOpen_finite_intersection_closure (T : BHistIndexedOpenCarrier)
    {S : BHist -> Prop} {i j : T.OpenIx} {h : BHist} :
    UnaryHistory h ->
      ((S h ∧ T.OpenAt (T.meet i j) h) <->
        ((S h ∧ T.OpenAt i h) ∧ (S h ∧ T.OpenAt j h))) :=
  BHistSubspaceOpen_finite_intersection T

theorem TopologySingleton_union_top_exactness {A : Type} {ι : A -> BHist} (a0 : A) :
    hsame (ι a0) BHist.Empty ->
      forall h : BHist,
        TopologySingletonOpenAt BHist.Empty h <->
          exists a : A, TopologySingletonOpenAt (ι a) h := by
  intro displayedTop h
  constructor
  · intro topOpen
    exact Exists.intro a0 (And.intro displayedTop topOpen.right)
  · intro indexedOpen
    cases indexedOpen with
    | intro a openA =>
        exact And.intro (hsame_refl BHist.Empty) openA.right

theorem TopologySingleton_union_case_split_ledger {A : Type} {ι : A -> BHist} :
    ((forall a : A, hsame (ι a) (BHist.e0 BHist.Empty)) ∨
      (exists a0 : A, hsame (ι a0) BHist.Empty)) ->
      exists accepted : BHist,
        (hsame accepted (BHist.e0 BHist.Empty) ∨ hsame accepted BHist.Empty) ∧
          forall h : BHist,
            TopologySingletonOpenAt accepted h <->
              exists a : A, TopologySingletonOpenAt (ι a) h := by
  intro ledger
  cases ledger with
  | inl allBottom =>
      exact Exists.intro (BHist.e0 BHist.Empty)
        (And.intro (Or.inl (hsame_refl (BHist.e0 BHist.Empty)))
          (TopologySingleton_union_bottom_exactness ι allBottom))
  | inr topMember =>
      cases topMember with
      | intro a0 topAt =>
          exact Exists.intro BHist.Empty
            (And.intro (Or.inr (hsame_refl BHist.Empty))
              (TopologySingleton_union_top_exactness (ι := ι) a0 topAt))

end BEDC.Derived.TopologyUp
