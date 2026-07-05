import Mathlib.Combinatorics.Pigeonhole

/-!
# ch8 有限读数必有纤维(定理 8.5)

有限读数即分类器:一个读数器把有限载体映到有限类集。当类少于读数时,鸽巢强制存在两个
不同读数落入同一类(非平凡纤维)。这是"分类劳动之无穷性"(评注 28.4 甲)的有限根据:
任何有限分类都留下纤维。
-/

namespace UnifiedTheory.Reading

/-- **定理 8.5(有限读数必有纤维)**:读数器 `read` 把有限载体 `carrier` 映入类集 `classes`,
    若类严格少于载体(`classes.card < carrier.card`),则存在两个不同元素同类(纤维)。 -/
theorem reading_has_fiber {α β : Type*} {carrier : Finset α} {classes : Finset β}
    (read : α → β) (hmaps : Set.MapsTo read carrier classes)
    (hcard : classes.card < carrier.card) :
    ∃ x ∈ carrier, ∃ y ∈ carrier, x ≠ y ∧ read x = read y :=
  Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps

end UnifiedTheory.Reading
