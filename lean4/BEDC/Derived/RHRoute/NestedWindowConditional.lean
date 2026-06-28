import BEDC.Derived.RHRoute.LocatedZetaZero
import BEDC.Derived.RHRoute.RationalPolygonWinding

namespace BEDC.Derived.RHRoute.NestedWindowConditional

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.LocatedZetaZero
open BEDC.Derived.RHRoute.ZetaBoxEvaluator

abbrev Rat : Type :=
  LocatedZetaZero.Rat

abbrev RatRect : Type :=
  LocatedZetaZero.RatRect

abbrev RatComplex : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

abbrev WindingPolygon : Type :=
  BEDC.Derived.RHRoute.RationalPolygonWinding.RationalPolygon

abbrev WindingApartEdges (polygon : WindingPolygon) : Type :=
  BEDC.Derived.RHRoute.RationalPolygonWinding.EdgeTubeApartList
    (BEDC.Derived.RHRoute.RationalPolygonWinding.polygonEdges polygon)

inductive ListMem {α : Type u} (x : α) : List α -> Prop where
  | head {tail : List α} : ListMem x (x :: tail)
  | tail {y : α} {tail : List α} :
      ListMem x tail -> ListMem x (y :: tail)

def RatRect.OnBoundary (R : RatRect) (z : RatComplex) : Prop :=
  R.ContainsPoint z ∧
    (RatEq z.re R.reLo ∨ RatEq z.re R.reHi ∨
      RatEq z.im R.imLo ∨ RatEq z.im R.imHi)

def PolygonSamplesBoundaryValues
    (F : RatComplex -> RatComplex) (R : RatRect)
    (polygon : WindingPolygon) : Prop :=
  forall value : RatComplex,
    ListMem value polygon.vertices ->
      ∃ z : RatComplex, R.OnBoundary z ∧ F z = value

structure BoundaryApart (F : RatComplex -> RatComplex)
    (R : RatRect) : Prop where
  boundary_nonzero :
    forall z : RatComplex, R.OnBoundary z -> F z = ratComplexZero -> False

structure BoundaryWinding (F : RatComplex -> RatComplex)
    (R : RatRect) where
  value : Int
  polygon : WindingPolygon
  boundary_values : PolygonSamplesBoundaryValues F R polygon
  apart_edges : WindingApartEdges polygon
  winding_eq :
    BEDC.Derived.RHRoute.RationalPolygonWinding.computedWinding polygon =
      value

def RectZero (F : RatComplex -> RatComplex) (R : RatRect) : Prop :=
  ∃ z : RatComplex, R.ContainsPoint z ∧ F z = ratComplexZero

def RatRectDiamLe (R : RatRect) (q : Rat) : Prop :=
  ratLe R.reWidth q ∧ ratLe R.imWidth q

structure NestedWindow (W : Nat -> RatRect) where
  nested : forall n : Nat, (W (Nat.succ n)).Subset (W n)
  diam : forall n : Nat, RatRectDiamLe (W n) (dyad n)
  centerPayload : CenterCauchyPayload W

def NestedWindow.reDiam {W : Nat -> RatRect}
    (window : NestedWindow W) :
    forall n : Nat, ratLe ((W n).reWidth) (dyad n) :=
  fun n => (window.diam n).left

def NestedWindow.imDiam {W : Nat -> RatRect}
    (window : NestedWindow W) :
    forall n : Nat, ratLe ((W n).imWidth) (dyad n) :=
  fun n => (window.diam n).right

def NestedWindow.located {W : Nat -> RatRect}
    (window : NestedWindow W) : LocatedComplex :=
  { R := W
    nested := window.nested
    reDiam := window.reDiam
    imDiam := window.imDiam
    centerPayload := window.centerPayload }

structure NestedWindowCert (F : RatComplex -> RatComplex)
    (W : Nat -> RatRect) extends NestedWindow W where
  boundary_apart : forall n : Nat, BoundaryApart F (W n)
  boundary_winding : forall n : Nat, BoundaryWinding F (W n)
  winding_one : forall n : Nat, (boundary_winding n).value = 1

structure DegreeExistenceHyp (F : RatComplex -> RatComplex) : Prop where
  exists_zero_of_winding_one :
    forall R : RatRect,
      BoundaryApart F R ->
        (winding : BoundaryWinding F R) ->
          winding.value = 1 ->
          RectZero F R

theorem zeros_in_every_window
    {F : RatComplex -> RatComplex} {W : Nat -> RatRect}
    (Deg : DegreeExistenceHyp F)
    (C : NestedWindowCert F W) :
    forall n : Nat, RectZero F (W n) := by
  intro n
  exact Deg.exists_zero_of_winding_one (W n)
    (C.boundary_apart n) (C.boundary_winding n) (C.winding_one n)

def CofinalWindowZeros (F : RatComplex -> RatComplex)
    (W : Nat -> RatRect) : Prop :=
  forall k : Nat, ∃ n : Nat, k ≤ n ∧ RectZero F (W n)

theorem cofinal_zeros_of_zeros_in_every_window
    {F : RatComplex -> RatComplex} {W : Nat -> RatRect}
    (hzero : forall n : Nat, RectZero F (W n)) :
    CofinalWindowZeros F W := by
  intro k
  exact Exists.intro k (And.intro (Nat.le_refl k) (hzero k))

def LocatedWindowVanishes (F : RatComplex -> RatComplex)
    (W : Nat -> RatRect) : Prop :=
  forall precision : Nat, ∃ n : Nat, precision ≤ n ∧ RectZero F (W n)

structure UniformContinuousOnNestedRects
    (F : RatComplex -> RatComplex) (W : Nat -> RatRect) : Prop where
  preserves_cofinal_window_zeros :
    CofinalWindowZeros F W -> LocatedWindowVanishes F W

structure LocatedZero (F : RatComplex -> RatComplex)
    (window : LocatedComplex) : Prop where
  zeros_in_window : forall n : Nat, RectZero F (window.R n)
  cofinal_zeros : CofinalWindowZeros F window.R
  continuity : UniformContinuousOnNestedRects F window.R
  vanishes_at_window : LocatedWindowVanishes F window.R

theorem located_zero_of_nested_windows
    {F : RatComplex -> RatComplex} {W : Nat -> RatRect}
    (Deg : DegreeExistenceHyp F)
    (C : NestedWindowCert F W)
    (UC : UniformContinuousOnNestedRects F W) :
    LocatedZero F C.toNestedWindow.located := by
  let hz : forall n : Nat, RectZero F (W n) :=
    zeros_in_every_window Deg C
  let cofinal : CofinalWindowZeros F W :=
    cofinal_zeros_of_zeros_in_every_window hz
  exact
    { zeros_in_window := hz
      cofinal_zeros := cofinal
      continuity := UC
      vanishes_at_window := UC.preserves_cofinal_window_zeros cofinal }

structure RhoNearWindowStream (W : Nat -> RatRect) where
  startsAtR0 : W 0 = LocatedZetaZero.rho_near_14_1347_R0

theorem rho_near_14_1347_conditional_zero
    (Zeta : RatComplex -> RatComplex)
    (rho_near_14_1347 : LocatedComplex)
    (anchor : RhoNearWindowStream rho_near_14_1347.R)
    (Deg : DegreeExistenceHyp Zeta)
    (C : NestedWindowCert Zeta rho_near_14_1347.R)
    (UC : UniformContinuousOnNestedRects Zeta rho_near_14_1347.R) :
    LocatedZero Zeta rho_near_14_1347 := by
  let _anchorReadback :
      rho_near_14_1347.R 0 = LocatedZetaZero.rho_near_14_1347_R0 :=
    anchor.startsAtR0
  let hz : forall n : Nat, RectZero Zeta (rho_near_14_1347.R n) :=
    zeros_in_every_window Deg C
  let cofinal : CofinalWindowZeros Zeta rho_near_14_1347.R :=
    cofinal_zeros_of_zeros_in_every_window hz
  exact
    { zeros_in_window := hz
      cofinal_zeros := cofinal
      continuity := UC
      vanishes_at_window := UC.preserves_cofinal_window_zeros cofinal }

end BEDC.Derived.RHRoute.NestedWindowConditional
