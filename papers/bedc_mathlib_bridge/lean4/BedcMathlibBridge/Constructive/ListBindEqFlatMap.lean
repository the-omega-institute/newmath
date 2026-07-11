import Mathlib.Data.List.Basic

namespace BedcMathlibBridge.Constructive.ListBindEqFlatMap

universe u

private def mathlibListBindEqFlatMapProvenanceAnchor : Unit :=
  let _ :
      {α β : Type u} → (f : α → List β) → (l : List α) →
        l >>= f = List.flatMap f l :=
    List.bind_eq_flatMap
  ()

def bindEqFlatMapReadback {α β : Type u} (f : α → List β) (l : List α) :
    l >>= f = List.flatMap f l :=
  let _ := mathlibListBindEqFlatMapProvenanceAnchor.{u}
  List.bind_eq_flatMap f l

theorem bindEqFlatMapReadback_eq_list_bind_eq_flatMap
    {α β : Type u} (f : α → List β) (l : List α) :
    bindEqFlatMapReadback f l = List.bind_eq_flatMap f l := by
  rfl

end BedcMathlibBridge.Constructive.ListBindEqFlatMap
