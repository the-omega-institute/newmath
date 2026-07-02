import BEDC.Derived.Visions.ObservationSectionCoherence
import Mathlib.Data.List.Basic
import Mathlib.CategoryTheory.Functor.Basic

namespace BedcMathlibBridge.Constructive.ObservationSectionCoherence

open CategoryTheory
open BEDC.Derived.Visions.ObservationSectionCoherence

universe u v w x

private def mathlibListPrefixProvenanceAnchor (W : Type u) : Unit :=
  let _ :
      ∀ {l₁ l₂ : List W} [BEq W] [LawfulBEq W],
        List.IsPrefix l₁ l₂ -> ∀ a : W, List.idxOf a l₁ ≤ List.idxOf a l₂ :=
    fun h a => List.IsPrefix.idxOf_le h a
  ()

private def mathlibFunctorProvenanceAnchor
    (C : Type u) (D : Type w) [Category.{v} C] [Category.{x} D] : Unit :=
  let _ :
      ∀ (F : C ⥤ D),
        ∀ {R S T : C} (f : R ⟶ S) (g : S ⟶ T),
          F.map (f ≫ g) = F.map f ≫ F.map g :=
    fun F => F.map_comp
  ()

def mathlibListPrefix {W : Type u} (l l' : Ledger W) : Prop :=
  let _ := mathlibListPrefixProvenanceAnchor W
  List.IsPrefix l l'

theorem mathlibListPrefix_iff_listIsPrefix {W : Type u}
    (l l' : Ledger W) :
    mathlibListPrefix l l' ↔ List.IsPrefix l l' := by
  rfl

theorem prefixLe_iff_mathlibListPrefix {W : Type u}
    (l l' : Ledger W) :
    prefixLe l l' ↔ mathlibListPrefix l l' := by
  unfold prefixLe mathlibListPrefix
  constructor
  · intro h
    cases h with
    | intro d hd =>
        exists d
        exact hd.symm
  · intro h
    cases h with
    | intro d hd =>
        exists d
        exact hd.symm

def frameCategory (F : FrameCat.{u, v}) : Category.{v} F.Obj where
  Hom R S := F.Hom R S
  id R := F.id R
  comp f g := F.comp g f
  id_comp := by
    intro R S f
    exact F.id_right f
  comp_id := by
    intro R S f
    exact F.id_left f
  assoc := by
    intro R S T U f g h
    exact F.assoc h g f

def hilbertCategory (H : HilbertLikeCat.{w, x}) : Category.{x} H.Obj where
  Hom R S := H.Hom R S
  id R := H.id R
  comp f g := H.comp g f
  id_comp := by
    intro R S f
    exact H.id_right f
  comp_id := by
    intro R S f
    exact H.id_left f
  assoc := by
    intro R S T U f g h
    exact H.assoc h g f

def mathlibThinBase (F : FrameCat.{u, v}) : Prop :=
  letI : Category.{v} F.Obj := frameCategory F
  let _ := mathlibFunctorProvenanceAnchor F.Obj F.Obj
  ∀ R S : F.Obj, Subsingleton (F.Hom R S)

theorem thinBase_iff_mathlibThinBase (F : FrameCat.{u, v}) :
    ThinBase F ↔ mathlibThinBase F := by
  constructor
  · intro hthin
    unfold mathlibThinBase
    dsimp
    intro R S
    exact ⟨fun f g => hthin R S f g⟩
  · intro hthin R S f g
    unfold mathlibThinBase at hthin
    dsimp at hthin
    exact (hthin R S).elim f g

def toMathlibFunctor
    {F : FrameCat.{u, v}} {H : HilbertLikeCat.{w, x}}
    (Phi : SectionBundleFunctor F H) :
    letI : Category.{v} F.Obj := frameCategory F
    letI : Category.{x} H.Obj := hilbertCategory H
    F.Obj ⥤ H.Obj :=
  letI : Category.{v} F.Obj := frameCategory F
  letI : Category.{x} H.Obj := hilbertCategory H
  let _ := mathlibFunctorProvenanceAnchor F.Obj H.Obj
  { obj := Phi.objMap
    map := fun f => Phi.homMap f
    map_id := by
      intro R
      exact Phi.map_id R
    map_comp := by
      intro R S T f g
      exact Phi.map_comp g f }

theorem toMathlibFunctor_obj
    {F : FrameCat.{u, v}} {H : HilbertLikeCat.{w, x}}
    (Phi : SectionBundleFunctor F H) (R : F.Obj) :
    let _ : Category.{v} F.Obj := frameCategory F
    let _ : Category.{x} H.Obj := hilbertCategory H
    (toMathlibFunctor Phi).obj R = Phi.objMap R := by
  rfl

theorem toMathlibFunctor_map_comp
    {F : FrameCat.{u, v}} {H : HilbertLikeCat.{w, x}}
    (Phi : SectionBundleFunctor F H)
    {R S T : F.Obj} (f : F.Hom R S) (g : F.Hom S T) :
    let _ : Category.{v} F.Obj := frameCategory F
    let _ : Category.{x} H.Obj := hilbertCategory H
    (toMathlibFunctor Phi).map (f ≫ g) =
      (toMathlibFunctor Phi).map f ≫ (toMathlibFunctor Phi).map g := by
  exact Phi.map_comp g f

theorem toMathlibFunctor_map_id
    {F : FrameCat.{u, v}} {H : HilbertLikeCat.{w, x}}
    (Phi : SectionBundleFunctor F H) (R : F.Obj) :
    let _ : Category.{v} F.Obj := frameCategory F
    let _ : Category.{x} H.Obj := hilbertCategory H
    (toMathlibFunctor Phi).map (𝟙 R) = 𝟙 (Phi.objMap R) := by
  exact Phi.map_id R

end BedcMathlibBridge.Constructive.ObservationSectionCoherence
