import BedcMathlibBridge.Constructive.ListBindEqFlatMap

namespace BedcMathlibBridge.Export.ListBindEqFlatMap

open BedcMathlibBridge.Constructive.ListBindEqFlatMap

universe u

structure ListBindEqFlatMapExportWitness where
  readback :
    {α β : Type u} → (f : α → List β) → (l : List α) →
      l >>= f = List.flatMap f l
  readback_apply :
    ∀ {α β : Type u} (f : α → List β) (l : List α),
      readback f l = bindEqFlatMapReadback f l
  mathlib_apply :
    ∀ {α β : Type u} (f : α → List β) (l : List α),
      readback f l = List.bind_eq_flatMap f l
  mathlib_anchor :
    {α β : Type u} → (f : α → List β) → (l : List α) →
      l >>= f = List.flatMap f l
  mathlib_anchor_apply :
    ∀ {α β : Type u} (f : α → List β) (l : List α),
      mathlib_anchor f l = List.bind_eq_flatMap f l

def listBindEqFlatMapExport : ListBindEqFlatMapExportWitness where
  readback := bindEqFlatMapReadback
  readback_apply := by
    intro α β f l
    rfl
  mathlib_apply := bindEqFlatMapReadback_eq_list_bind_eq_flatMap
  mathlib_anchor := List.bind_eq_flatMap
  mathlib_anchor_apply := by
    intro α β f l
    rfl

theorem list_bind_eq_flatMap_mathlib_correspondence
    {α β : Type u} (f : α → List β) (l : List α) :
    bindEqFlatMapReadback f l = List.bind_eq_flatMap f l := by
  exact bindEqFlatMapReadback_eq_list_bind_eq_flatMap f l

end BedcMathlibBridge.Export.ListBindEqFlatMap
