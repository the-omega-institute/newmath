import BedcMathlibBridge.Constructive.ObservationSectionCoherence

namespace BedcMathlibBridge.Export.ObservationSectionCoherence

namespace C := BedcMathlibBridge.Constructive.ObservationSectionCoherence

open CategoryTheory
open BEDC.Derived.Visions.ObservationSectionCoherence

universe u v w x

structure ObservationPrefixExportWitness where
  readback : ∀ {W : Type u}, Ledger W -> Ledger W -> Prop
  readback_apply : ∀ {W : Type u} (l l' : Ledger W),
    readback l l' = C.mathlibListPrefix l l'
  bedc_prefix_apply : ∀ {W : Type u} (l l' : Ledger W),
    prefixLe l l' ↔ readback l l'
  list_prefix_apply : ∀ {W : Type u} (l l' : Ledger W),
    readback l l' ↔ List.IsPrefix l l'

def observationPrefixExport : ObservationPrefixExportWitness where
  readback := C.mathlibListPrefix
  readback_apply := by
    intro W l l'
    rfl
  bedc_prefix_apply := by
    intro W l l'
    exact C.prefixLe_iff_mathlibListPrefix l l'
  list_prefix_apply := by
    intro W l l'
    exact C.mathlibListPrefix_iff_listIsPrefix l l'

theorem prefixLe_iff_listIsPrefix {W : Type u} (l l' : Ledger W) :
    prefixLe l l' ↔ List.IsPrefix l l' := by
  exact (observationPrefixExport.bedc_prefix_apply l l').trans
    (observationPrefixExport.list_prefix_apply l l')

structure SectionBundleFunctorExportWitness where
  frameCategory :
    ∀ (F : FrameCat.{u, v}), Category.{v} F.Obj
  hilbertCategory :
    ∀ (H : HilbertLikeCat.{w, x}), Category.{x} H.Obj
  toFunctor :
    ∀ {F : FrameCat.{u, v}} {H : HilbertLikeCat.{w, x}},
      SectionBundleFunctor F H ->
        letI : Category.{v} F.Obj := frameCategory F
        letI : Category.{x} H.Obj := hilbertCategory H
        F.Obj ⥤ H.Obj
  thin_base_apply :
    ∀ (F : FrameCat.{u, v}), ThinBase F ↔ C.mathlibThinBase F
  obj_apply :
    ∀ {F : FrameCat.{u, v}} {H : HilbertLikeCat.{w, x}}
      (Phi : SectionBundleFunctor F H) (R : F.Obj),
        letI : Category.{v} F.Obj := frameCategory F
        letI : Category.{x} H.Obj := hilbertCategory H
        (toFunctor Phi).obj R = Phi.objMap R
  map_comp_apply :
    ∀ {F : FrameCat.{u, v}} {H : HilbertLikeCat.{w, x}}
      (Phi : SectionBundleFunctor F H)
      {R S T : F.Obj} (f : F.Hom R S) (g : F.Hom S T),
        letI : Category.{v} F.Obj := frameCategory F
        letI : Category.{x} H.Obj := hilbertCategory H
        (toFunctor Phi).map (f ≫ g) =
          (toFunctor Phi).map f ≫ (toFunctor Phi).map g
  map_id_apply :
    ∀ {F : FrameCat.{u, v}} {H : HilbertLikeCat.{w, x}}
      (Phi : SectionBundleFunctor F H) (R : F.Obj),
        letI : Category.{v} F.Obj := frameCategory F
        letI : Category.{x} H.Obj := hilbertCategory H
        (toFunctor Phi).map (𝟙 R) = 𝟙 (Phi.objMap R)

def sectionBundleFunctorExport : SectionBundleFunctorExportWitness where
  frameCategory := C.frameCategory
  hilbertCategory := C.hilbertCategory
  toFunctor := C.toMathlibFunctor
  thin_base_apply := C.thinBase_iff_mathlibThinBase
  obj_apply := by
    intro F H Phi R
    exact C.toMathlibFunctor_obj Phi R
  map_comp_apply := by
    intro F H Phi R S T f g
    exact C.toMathlibFunctor_map_comp Phi f g
  map_id_apply := by
    intro F H Phi R
    exact C.toMathlibFunctor_map_id Phi R

structure ObservationPrefixMathlibCorrespondence where
  prefix_apply :
    ∀ {W : Type u} (l l' : Ledger W), prefixLe l l' ↔ List.IsPrefix l l'
  trans_apply :
    ∀ {W : Type u} {l l' l'' : Ledger W},
      prefixLe l l' -> prefixLe l' l'' -> prefixLe l l''
  mathlib_idxOf_surface :
    ∀ {W : Type u} {l l' : List W} [BEq W] [LawfulBEq W],
      List.IsPrefix l l' -> ∀ a : W, List.idxOf a l ≤ List.idxOf a l'

def observation_prefix_mathlib_correspondence :
    ObservationPrefixMathlibCorrespondence where
  prefix_apply := prefixLe_iff_listIsPrefix
  trans_apply := by
    intro W l l' l'' hll' hl'l''
    exact prefixLe_trans hll' hl'l''
  mathlib_idxOf_surface := by
    intro W l l' instBEq instLawful h a
    exact List.IsPrefix.idxOf_le h a

structure SectionBundleFunctorMathlibCorrespondence where
  thin_base_apply :
    ∀ (F : FrameCat.{u, v}), ThinBase F ↔ C.mathlibThinBase F
  comp_apply :
    ∀ {F : FrameCat.{u, v}} {H : HilbertLikeCat.{w, x}}
      (Phi : SectionBundleFunctor F H)
      {R S T : F.Obj} (f : F.Hom R S) (g : F.Hom S T),
        letI : Category.{v} F.Obj := C.frameCategory F
        letI : Category.{x} H.Obj := C.hilbertCategory H
        (C.toMathlibFunctor Phi).map (f ≫ g) =
          (C.toMathlibFunctor Phi).map f ≫ (C.toMathlibFunctor Phi).map g
  id_apply :
    ∀ {F : FrameCat.{u, v}} {H : HilbertLikeCat.{w, x}}
      (Phi : SectionBundleFunctor F H) (R : F.Obj),
        letI : Category.{v} F.Obj := C.frameCategory F
        letI : Category.{x} H.Obj := C.hilbertCategory H
        (C.toMathlibFunctor Phi).map (𝟙 R) = 𝟙 (Phi.objMap R)

def section_bundle_functor_mathlib_correspondence :
    SectionBundleFunctorMathlibCorrespondence where
  thin_base_apply := C.thinBase_iff_mathlibThinBase
  comp_apply := by
    intro F H Phi R S T f g
    exact C.toMathlibFunctor_map_comp Phi f g
  id_apply := by
    intro F H Phi R
    exact C.toMathlibFunctor_map_id Phi R

end BedcMathlibBridge.Export.ObservationSectionCoherence
