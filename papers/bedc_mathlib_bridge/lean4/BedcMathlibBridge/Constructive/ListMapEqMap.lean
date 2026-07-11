import Mathlib.Data.List.Basic

namespace BedcMathlibBridge.Constructive.ListMapEqMap

universe u

private def mathlibListMapEqMapProvenanceAnchor : Unit :=
  let _ : {α β : Type u} → (f : α → β) → (l : List α) → f <$> l = List.map f l :=
    List.map_eq_map
  ()

def mapEqMapReadback {α β : Type u} (f : α → β) (l : List α) :
    f <$> l = List.map f l :=
  let _ := mathlibListMapEqMapProvenanceAnchor.{u}
  List.map_eq_map f l

theorem mapEqMapReadback_eq_list_map_eq_map {α β : Type u}
    (f : α → β) (l : List α) :
    mapEqMapReadback f l = List.map_eq_map f l := by
  rfl

end BedcMathlibBridge.Constructive.ListMapEqMap
