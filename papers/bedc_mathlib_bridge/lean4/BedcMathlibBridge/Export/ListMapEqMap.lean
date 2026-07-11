import BedcMathlibBridge.Constructive.ListMapEqMap

namespace BedcMathlibBridge.Export.ListMapEqMap

open BedcMathlibBridge.Constructive.ListMapEqMap

universe u

structure ListMapEqMapExportWitness where
  readback :
    {α β : Type u} → (f : α → β) → (l : List α) → f <$> l = List.map f l
  readback_apply :
    ∀ {α β : Type u} (f : α → β) (l : List α),
      readback f l = mapEqMapReadback f l
  mathlib_apply :
    ∀ {α β : Type u} (f : α → β) (l : List α),
      readback f l = List.map_eq_map f l
  mathlib_anchor :
    {α β : Type u} → (f : α → β) → (l : List α) → f <$> l = List.map f l
  mathlib_anchor_apply :
    ∀ {α β : Type u} (f : α → β) (l : List α),
      mathlib_anchor f l = List.map_eq_map f l

def listMapEqMapExport : ListMapEqMapExportWitness where
  readback := mapEqMapReadback
  readback_apply := by
    intro α β f l
    rfl
  mathlib_apply := mapEqMapReadback_eq_list_map_eq_map
  mathlib_anchor := List.map_eq_map
  mathlib_anchor_apply := by
    intro α β f l
    rfl

theorem list_map_eq_map_mathlib_correspondence
    {α β : Type u} (f : α → β) (l : List α) :
    mapEqMapReadback f l = List.map_eq_map f l := by
  exact mapEqMapReadback_eq_list_map_eq_map f l

end BedcMathlibBridge.Export.ListMapEqMap
