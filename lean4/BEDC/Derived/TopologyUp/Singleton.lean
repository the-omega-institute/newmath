import BEDC.Derived.TopologyUp

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def TopologySingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def TopologySingletonOpenAt (i h : BHist) : Prop :=
  hsame i BHist.Empty ∧ TopologySingletonCarrier h

def TopologySingletonMeet (i j : BHist) : BHist :=
  match i, j with
  | BHist.Empty, BHist.Empty => BHist.Empty
  | BHist.Empty, BHist.e0 _ => BHist.e0 BHist.Empty
  | BHist.Empty, BHist.e1 _ => BHist.e0 BHist.Empty
  | BHist.e0 _, BHist.Empty => BHist.e0 BHist.Empty
  | BHist.e0 _, BHist.e0 _ => BHist.e0 BHist.Empty
  | BHist.e0 _, BHist.e1 _ => BHist.e0 BHist.Empty
  | BHist.e1 _, BHist.Empty => BHist.e0 BHist.Empty
  | BHist.e1 _, BHist.e0 _ => BHist.e0 BHist.Empty
  | BHist.e1 _, BHist.e1 _ => BHist.e0 BHist.Empty

theorem TopologySingleton_semantic_name_certificate :
    SemanticNameCert TopologySingletonCarrier TopologySingletonCarrier TopologySingletonCarrier
      (fun h k : BHist => TopologySingletonCarrier h ∧ TopologySingletonCarrier k ∧ hsame h k) ∧
      (forall h : BHist, TopologySingletonOpenAt (BHist.e0 BHist.Empty) h <-> False) ∧
      (forall h : BHist,
        TopologySingletonOpenAt BHist.Empty h <-> TopologySingletonCarrier h) := by
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro BHist.Empty (hsame_refl BHist.Empty)
        equiv_refl := by
          intro h carrierH
          exact And.intro carrierH (And.intro carrierH (hsame_refl h))
        equiv_symm := by
          intro h k classified
          exact And.intro classified.right.left
            (And.intro classified.left (hsame_symm classified.right.right))
        equiv_trans := by
          intro h k r classifiedHK classifiedKR
          exact And.intro classifiedHK.left
            (And.intro classifiedKR.right.left
              (hsame_trans classifiedHK.right.right classifiedKR.right.right))
        carrier_respects_equiv := by
          intro h k classified _carrierH
          exact classified.right.left
      }
      pattern_sound := by
        intro h sourceH
        exact sourceH
      ledger_sound := by
        intro h sourceH
        exact sourceH
    }
  · constructor
    · intro h
      constructor
      · intro openH
        exact not_hsame_e0_empty openH.left
      · intro impossible
        exact False.elim impossible
    · intro h
      constructor
      · intro openH
        exact openH.right
      · intro carrierH
        exact And.intro (hsame_refl BHist.Empty) carrierH

theorem TopologySingleton_finite_intersection_laws
    {i j h : BHist}
    (_validI : hsame i BHist.Empty ∨ hsame i (BHist.e0 BHist.Empty))
    (_validJ : hsame j BHist.Empty ∨ hsame j (BHist.e0 BHist.Empty)) :
    TopologySingletonOpenAt (TopologySingletonMeet i j) h <->
      TopologySingletonOpenAt i h ∧ TopologySingletonOpenAt j h := by
  cases i with
  | Empty =>
      cases j with
      | Empty =>
          constructor
          · intro openMeet
            exact And.intro openMeet openMeet
          · intro openBoth
            exact openBoth.left
      | e0 t =>
          constructor
          · intro openMeet
            exact False.elim (not_hsame_e0_empty openMeet.left)
          · intro openBoth
            exact False.elim (not_hsame_e0_empty openBoth.right.left)
      | e1 t =>
          constructor
          · intro openMeet
            exact False.elim (not_hsame_e0_empty openMeet.left)
          · intro openBoth
            exact False.elim (not_hsame_e1_empty openBoth.right.left)
  | e0 t =>
      cases j with
      | Empty =>
          constructor
          · intro openMeet
            exact False.elim (not_hsame_e0_empty openMeet.left)
          · intro openBoth
            exact False.elim (not_hsame_e0_empty openBoth.left.left)
      | e0 u =>
          constructor
          · intro openMeet
            exact False.elim (not_hsame_e0_empty openMeet.left)
          · intro openBoth
            exact False.elim (not_hsame_e0_empty openBoth.left.left)
      | e1 u =>
          constructor
          · intro openMeet
            exact False.elim (not_hsame_e0_empty openMeet.left)
          · intro openBoth
            exact False.elim (not_hsame_e0_empty openBoth.left.left)
  | e1 t =>
      cases j with
      | Empty =>
          constructor
          · intro openMeet
            exact False.elim (not_hsame_e0_empty openMeet.left)
          · intro openBoth
            exact False.elim (not_hsame_e1_empty openBoth.left.left)
      | e0 u =>
          constructor
          · intro openMeet
            exact False.elim (not_hsame_e0_empty openMeet.left)
          · intro openBoth
            exact False.elim (not_hsame_e1_empty openBoth.left.left)
      | e1 u =>
          constructor
          · intro openMeet
            exact False.elim (not_hsame_e0_empty openMeet.left)
          · intro openBoth
            exact False.elim (not_hsame_e1_empty openBoth.left.left)

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
