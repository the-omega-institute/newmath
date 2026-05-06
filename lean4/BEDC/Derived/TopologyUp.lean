import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

def BHistPullbackOpen (f : BHist -> BHist) (U : BHist -> Prop) (y : BHist) :
    Prop :=
  U (f y)

def BHistPullbackCarriesOpen (T : BHistIndexedOpenCarrier) (f : BHist -> BHist)
    (i : T.OpenIx) (U : BHist -> Prop) : Prop :=
  forall {y : BHist}, UnaryHistory y -> UnaryHistory (f y) ->
    (BHistPullbackOpen f U y <-> T.OpenAt i (f y))

theorem BHistPullbackOpen_finite_meet (T : BHistIndexedOpenCarrier)
    {f : BHist -> BHist} {i j : T.OpenIx} {U V : BHist -> Prop} :
    BHistPullbackCarriesOpen T f i U ->
      BHistPullbackCarriesOpen T f j V ->
        BHistPullbackCarriesOpen T f (T.meet i j) (fun x : BHist => U x ∧ V x) := by
  intro carryU carryV y unaryY unaryImage
  have uAt : BHistPullbackOpen f U y <-> T.OpenAt i (f y) :=
    carryU unaryY unaryImage
  have vAt : BHistPullbackOpen f V y <-> T.OpenAt j (f y) :=
    carryV unaryY unaryImage
  have meetAt : T.OpenAt (T.meet i j) (f y) <->
      (T.OpenAt i (f y) ∧ T.OpenAt j (f y)) :=
    T.meet_law unaryImage
  constructor
  · intro pullbackBoth
    have openU : T.OpenAt i (f y) := Iff.mp uAt pullbackBoth.left
    have openV : T.OpenAt j (f y) := Iff.mp vAt pullbackBoth.right
    exact Iff.mpr meetAt (And.intro openU openV)
  · intro openMeet
    have openBoth : T.OpenAt i (f y) ∧ T.OpenAt j (f y) := Iff.mp meetAt openMeet
    exact And.intro (Iff.mpr uAt openBoth.left) (Iff.mpr vAt openBoth.right)

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

theorem BHistPullbackOpen_finite_meet_transport (T : BHistIndexedOpenCarrier)
    {i j : T.OpenIx} {U V : BHist -> Prop} {f : BHist -> BHist}
    (mapUnary : forall {y : BHist}, UnaryHistory y -> UnaryHistory (f y))
    (mapSame :
      forall {y z : BHist}, UnaryHistory y -> UnaryHistory z -> hsame y z ->
        hsame (f y) (f z))
    (carryU : BHistCarriesOpen T i U) (carryV : BHistCarriesOpen T j V) :
    (forall {y : BHist}, UnaryHistory y ->
      ((U (f y) ∧ V (f y)) <-> T.OpenAt (T.meet i j) (f y))) ∧
      (forall {y z : BHist}, UnaryHistory y -> UnaryHistory z -> hsame y z ->
        ((U (f y) ∧ V (f y)) <-> (U (f z) ∧ V (f z)))) := by
  have meetCarry :
      forall {y : BHist}, UnaryHistory y ->
        ((U (f y) ∧ V (f y)) <-> T.OpenAt (T.meet i j) (f y)) := by
    intro y unaryY
    have unaryFY : UnaryHistory (f y) := mapUnary unaryY
    have carryUY : U (f y) <-> T.OpenAt i (f y) := carryU unaryFY
    have carryVY : V (f y) <-> T.OpenAt j (f y) := carryV unaryFY
    have meetAt :
        T.OpenAt (T.meet i j) (f y) <-> T.OpenAt i (f y) ∧ T.OpenAt j (f y) :=
      T.meet_law unaryFY
    constructor
    · intro both
      exact Iff.mpr meetAt (And.intro (Iff.mp carryUY both.left) (Iff.mp carryVY both.right))
    · intro openMeet
      have openBoth : T.OpenAt i (f y) ∧ T.OpenAt j (f y) := Iff.mp meetAt openMeet
      exact And.intro (Iff.mpr carryUY openBoth.left) (Iff.mpr carryVY openBoth.right)
  constructor
  · exact meetCarry
  · intro y z unaryY unaryZ sameYZ
    have unaryFY : UnaryHistory (f y) := mapUnary unaryY
    have unaryFZ : UnaryHistory (f z) := mapUnary unaryZ
    have sameF : hsame (f y) (f z) := mapSame unaryY unaryZ sameYZ
    have stable :
        T.OpenAt (T.meet i j) (f y) <-> T.OpenAt (T.meet i j) (f z) :=
      T.membership_stable unaryFY unaryFZ sameF
    have carryY : (U (f y) ∧ V (f y)) <-> T.OpenAt (T.meet i j) (f y) :=
      meetCarry unaryY
    have carryZ : (U (f z) ∧ V (f z)) <-> T.OpenAt (T.meet i j) (f z) :=
      meetCarry unaryZ
    constructor
    · intro bothY
      have openY : T.OpenAt (T.meet i j) (f y) := Iff.mp carryY bothY
      have openZ : T.OpenAt (T.meet i j) (f z) := Iff.mp stable openY
      exact Iff.mpr carryZ openZ
    · intro bothZ
      have openZ : T.OpenAt (T.meet i j) (f z) := Iff.mp carryZ bothZ
      have openY : T.OpenAt (T.meet i j) (f y) := Iff.mpr stable openZ
      exact Iff.mpr carryY openY

def BHistGeneratedOpenExact (T : BHistIndexedOpenCarrier) (U : BHist -> Prop) :
    Prop :=
  exists i : T.OpenIx, BHistCarriesOpen T i U

theorem BHistGeneratedOpen_binary_meet_admission (T : BHistIndexedOpenCarrier)
    {U V : BHist -> Prop} :
    BHistGeneratedOpenExact T U ->
      BHistGeneratedOpenExact T V ->
        BHistGeneratedOpenExact T (fun x : BHist => U x ∧ V x) ∧
          (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
            ((U x ∧ V x) <-> (U y ∧ V y))) := by
  intro exactU exactV
  cases exactU with
  | intro i carryU =>
      cases exactV with
      | intro j carryV =>
          have closure :=
            BHistIndexedOpen_finite_intersection_closure (T := T) (i := i) (j := j)
              (U := U) (V := V) carryU carryV
          exact And.intro (Exists.intro (T.meet i j) closure.left) closure.right

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
  · exact TopologySingleton_boundary_open_laws

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

end BEDC.Derived.TopologyUp
