import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Substitution
import BEDC.MetaCIC.ClosedTerm

namespace BEDC.MetaCIC

theorem substitute_compose_closed_both_at_depth
    {d : Idx} (v u t : Term)
    (_hv : ClosedAt 0 v) (hu : ClosedAt 0 u)
    (ht : ClosedAt (d + 1) t) :
    substitute d v (substitute d u t) =
      substitute d (substitute d v u) t := by
  have hinner : ClosedAt d (substitute d u t) := by
    exact substitute_closed_source_closes_anchor_via_term_induction d hu ht
  rw [substitute_closed d v (substitute d u t) hinner]
  have hu_at_d : ClosedAt d u := by
    exact closedAt_zero_at d u hu
  rw [substitute_closed d v u hu_at_d]

theorem substitute_compose_closed_both
    (v u t : Term)
    (hv : ClosedAt 0 v) (hu : ClosedAt 0 u)
    (ht : ClosedAt 1 t) :
    substitute 0 v (substitute 0 u t) =
      substitute 0 (substitute 0 v u) t := by
  exact substitute_compose_closed_both_at_depth
    (d := 0) v u t hv hu ht

theorem substitute_swap_closed
    {d : Idx} (v u t : Term)
    (_hv : ClosedAt 0 v) (_hu : ClosedAt 0 u)
    (ht : ClosedAt d t) :
    substitute d v (substitute d u t) =
      substitute d u (substitute d v t) := by
  rw [substitute_closed d u t ht]
  rw [substitute_closed d v t ht]
  rw [substitute_closed d u t ht]

theorem substitute_after_shift_one_closed
    (v t : Term) (_hv : ClosedAt 0 v) :
    substitute 0 v (shift 0 1 t) = t := by
  exact substitute_shift_at_eq 0 v t

end BEDC.MetaCIC
