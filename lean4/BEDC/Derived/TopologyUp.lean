import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

structure BHistIndexedOpenCarrier where
  OpenIx : Type
  OpenAt : OpenIx -> BHist -> Prop
  meet : OpenIx -> OpenIx -> OpenIx
  membership_stable :
    forall {i : OpenIx} {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
      (OpenAt i x <-> OpenAt i y)
  meet_law :
    forall {i j : OpenIx} {x : BHist}, UnaryHistory x ->
      (OpenAt (meet i j) x <-> (OpenAt i x ∧ OpenAt j x))

def BHistCarriesOpen (T : BHistIndexedOpenCarrier) (i : T.OpenIx)
    (U : BHist -> Prop) : Prop :=
  forall {x : BHist}, UnaryHistory x -> (U x <-> T.OpenAt i x)

structure BHistIndexedBoundaryOpen (T : BHistIndexedOpenCarrier) where
  bottom : T.OpenIx
  top : T.OpenIx
  bottom_law : forall {x : BHist}, UnaryHistory x -> (T.OpenAt bottom x <-> False)
  top_law : forall {x : BHist}, UnaryHistory x -> (T.OpenAt top x <-> True)

theorem BHistCarriesOpen_classifier_transport (T : BHistIndexedOpenCarrier)
    {i : T.OpenIx} {U : BHist -> Prop} :
    BHistCarriesOpen T i U ->
      forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y -> (U x <-> U y) := by
  intro carries x y unaryX unaryY sameXY
  have carryX : U x <-> T.OpenAt i x :=
    carries unaryX
  have carryY : U y <-> T.OpenAt i y :=
    carries unaryY
  have stable : T.OpenAt i x <-> T.OpenAt i y :=
    T.membership_stable unaryX unaryY sameXY
  constructor
  · intro ux
    have openX : T.OpenAt i x :=
      Iff.mp carryX ux
    have openY : T.OpenAt i y :=
      Iff.mp stable openX
    exact Iff.mpr carryY openY
  · intro uy
    have openY : T.OpenAt i y :=
      Iff.mp carryY uy
    have openX : T.OpenAt i x :=
      Iff.mpr stable openY
    exact Iff.mpr carryX openX

theorem BHistIndexedOpen_finite_intersection_closure (T : BHistIndexedOpenCarrier)
    {i j : T.OpenIx} {U V : BHist -> Prop} :
    BHistCarriesOpen T i U -> BHistCarriesOpen T j V ->
      BHistCarriesOpen T (T.meet i j) (fun x : BHist => U x ∧ V x) ∧
        (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
          ((U x ∧ V x) <-> (U y ∧ V y))) := by
  intro carryU carryV
  have meetCarries :
      BHistCarriesOpen T (T.meet i j) (fun x : BHist => U x ∧ V x) := by
    intro x unaryX
    have uAt : U x <-> T.OpenAt i x := carryU unaryX
    have vAt : V x <-> T.OpenAt j x := carryV unaryX
    have meetAt :
        T.OpenAt (T.meet i j) x <-> (T.OpenAt i x ∧ T.OpenAt j x) :=
      T.meet_law unaryX
    constructor
    · intro both
      exact Iff.mpr meetAt (And.intro (Iff.mp uAt both.left) (Iff.mp vAt both.right))
    · intro openMeet
      have openBoth : T.OpenAt i x ∧ T.OpenAt j x := Iff.mp meetAt openMeet
      exact And.intro (Iff.mpr uAt openBoth.left) (Iff.mpr vAt openBoth.right)
  constructor
  · exact meetCarries
  · intro x y unaryX unaryY sameXY
    have carryX : (U x ∧ V x) <-> T.OpenAt (T.meet i j) x := meetCarries unaryX
    have carryY : (U y ∧ V y) <-> T.OpenAt (T.meet i j) y := meetCarries unaryY
    have stable :
        T.OpenAt (T.meet i j) x <-> T.OpenAt (T.meet i j) y :=
      T.membership_stable unaryX unaryY sameXY
    constructor
    · intro bothX
      have openX : T.OpenAt (T.meet i j) x := Iff.mp carryX bothX
      have openY : T.OpenAt (T.meet i j) y := Iff.mp stable openX
      exact Iff.mpr carryY openY
    · intro bothY
      have openY : T.OpenAt (T.meet i j) y := Iff.mp carryY bothY
      have openX : T.OpenAt (T.meet i j) x := Iff.mpr stable openY
      exact Iff.mpr carryX openX

theorem BHistIndexedOpen_arbitrary_union_closure (T : BHistIndexedOpenCarrier)
    {A : Type} {u : T.OpenIx} {ι : A -> T.OpenIx} {U : A -> BHist -> Prop} :
    (forall {x : BHist}, UnaryHistory x ->
      (T.OpenAt u x <-> exists a : A, T.OpenAt (ι a) x)) ->
    (forall a : A, BHistCarriesOpen T (ι a) (U a)) ->
      BHistCarriesOpen T u (fun x : BHist => exists a : A, U a x) ∧
        (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
          ((exists a : A, U a x) <-> (exists a : A, U a y))) := by
  intro unionLaw carries
  have unionCarries :
      BHistCarriesOpen T u (fun x : BHist => exists a : A, U a x) := by
    intro x unaryX
    have unionAt : T.OpenAt u x <-> exists a : A, T.OpenAt (ι a) x :=
      unionLaw unaryX
    constructor
    · intro existsU
      cases existsU with
      | intro a uaX =>
          have carryA : U a x <-> T.OpenAt (ι a) x := carries a unaryX
          have openA : T.OpenAt (ι a) x := Iff.mp carryA uaX
          exact Iff.mpr unionAt (Exists.intro a openA)
    · intro openUnion
      have existsOpen : exists a : A, T.OpenAt (ι a) x := Iff.mp unionAt openUnion
      cases existsOpen with
      | intro a openA =>
          have carryA : U a x <-> T.OpenAt (ι a) x := carries a unaryX
          exact Exists.intro a (Iff.mpr carryA openA)
  constructor
  · exact unionCarries
  · intro x y unaryX unaryY sameXY
    have carryX : (exists a : A, U a x) <-> T.OpenAt u x := unionCarries unaryX
    have carryY : (exists a : A, U a y) <-> T.OpenAt u y := unionCarries unaryY
    have stable : T.OpenAt u x <-> T.OpenAt u y :=
      T.membership_stable unaryX unaryY sameXY
    constructor
    · intro existsX
      have openX : T.OpenAt u x := Iff.mp carryX existsX
      have openY : T.OpenAt u y := Iff.mp stable openX
      exact Iff.mpr carryY openY
    · intro existsY
      have openY : T.OpenAt u y := Iff.mp carryY existsY
      have openX : T.OpenAt u x := Iff.mpr stable openY
      exact Iff.mpr carryX openX

theorem BHistIndexedOpen_boundary_closure (T : BHistIndexedOpenCarrier)
    (boundary : BHistIndexedBoundaryOpen T) :
    BHistCarriesOpen T boundary.bottom (fun _ : BHist => False) ∧
      BHistCarriesOpen T boundary.top (fun _ : BHist => True) ∧
        (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
          ((False : Prop) <-> False)) ∧
          (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
            ((True : Prop) <-> True)) := by
  have bottomCarries :
      BHistCarriesOpen T boundary.bottom (fun _ : BHist => False) := by
    intro x unaryX
    have bottomAt : T.OpenAt boundary.bottom x <-> False := boundary.bottom_law unaryX
    constructor
    · intro falseValue
      cases falseValue
    · intro openBottom
      exact Iff.mp bottomAt openBottom
  have topCarries :
      BHistCarriesOpen T boundary.top (fun _ : BHist => True) := by
    intro x unaryX
    have topAt : T.OpenAt boundary.top x <-> True := boundary.top_law unaryX
    constructor
    · intro trueValue
      exact Iff.mpr topAt trueValue
    · intro openTop
      exact Iff.mp topAt openTop
  have falseStable :
      forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
        ((False : Prop) <-> False) := by
    intro x y unaryX unaryY sameXY
    have stable :
        T.OpenAt boundary.bottom x <-> T.OpenAt boundary.bottom y :=
      T.membership_stable unaryX unaryY sameXY
    have bottomX : False <-> T.OpenAt boundary.bottom x := bottomCarries unaryX
    have bottomY : False <-> T.OpenAt boundary.bottom y := bottomCarries unaryY
    constructor
    · intro falseX
      have openX : T.OpenAt boundary.bottom x := Iff.mp bottomX falseX
      have openY : T.OpenAt boundary.bottom y := Iff.mp stable openX
      exact Iff.mpr bottomY openY
    · intro falseY
      have openY : T.OpenAt boundary.bottom y := Iff.mp bottomY falseY
      have openX : T.OpenAt boundary.bottom x := Iff.mpr stable openY
      exact Iff.mpr bottomX openX
  have trueStable :
      forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
        ((True : Prop) <-> True) := by
    intro x y unaryX unaryY sameXY
    have stable :
        T.OpenAt boundary.top x <-> T.OpenAt boundary.top y :=
      T.membership_stable unaryX unaryY sameXY
    have topX : True <-> T.OpenAt boundary.top x := topCarries unaryX
    have topY : True <-> T.OpenAt boundary.top y := topCarries unaryY
    constructor
    · intro trueX
      have openX : T.OpenAt boundary.top x := Iff.mp topX trueX
      have openY : T.OpenAt boundary.top y := Iff.mp stable openX
      exact Iff.mpr topY openY
    · intro trueY
      have openY : T.OpenAt boundary.top y := Iff.mp topY trueY
      have openX : T.OpenAt boundary.top x := Iff.mpr stable openY
      exact Iff.mpr topX openX
  exact And.intro bottomCarries (And.intro topCarries (And.intro falseStable trueStable))

def TopologySingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def TopologySingletonOpenAt (i h : BHist) : Prop :=
  hsame i BHist.Empty ∧ TopologySingletonCarrier h

theorem TopologySingleton_boundary_open_laws :
    (forall h : BHist, TopologySingletonOpenAt (BHist.e0 BHist.Empty) h <-> False) ∧
      (forall h : BHist,
        TopologySingletonOpenAt BHist.Empty h <-> TopologySingletonCarrier h) := by
  constructor
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

end BEDC.Derived.TopologyUp
