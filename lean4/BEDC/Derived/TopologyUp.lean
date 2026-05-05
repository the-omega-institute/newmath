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

end BEDC.Derived.TopologyUp
