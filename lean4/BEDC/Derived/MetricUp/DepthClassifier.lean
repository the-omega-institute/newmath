import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem MetricDistanceDepth_zero_iff_empty {d : BHist} :
    MetricDistanceDepth d = 0 ↔ hsame d BHist.Empty := by
  constructor
  · intro depthZero
    cases d with
    | Empty =>
        exact hsame_refl BHist.Empty
    | e0 d =>
        cases depthZero
    | e1 d =>
        cases depthZero
  · intro sameEmpty
    cases sameEmpty
    rfl

theorem MetricDistanceDepth_positive_iff_nonempty {d : BHist} :
    (0 < MetricDistanceDepth d) <-> (hsame d BHist.Empty -> False) := by
  constructor
  · intro positive sameEmpty
    cases d with
    | Empty =>
        cases positive
    | e0 d =>
        exact not_hsame_e0_empty sameEmpty
    | e1 d =>
        exact not_hsame_e1_empty sameEmpty
  · intro nonempty
    cases d with
    | Empty =>
        exact False.elim (nonempty (hsame_refl BHist.Empty))
    | e0 d =>
        exact Nat.succ_pos (MetricDistanceDepth d)
    | e1 d =>
        exact Nat.succ_pos (MetricDistanceDepth d)

theorem MetricDistanceDepth_positive_shape_cases {d : BHist} :
    (MetricDistanceDepth d = 0 -> False) ->
      (∃ z : BHist, d = BHist.e0 z) ∨ (∃ z : BHist, d = BHist.e1 z) := by
  intro positiveDepth
  cases d with
  | Empty =>
      exact False.elim (positiveDepth rfl)
  | e0 d =>
      left
      exact Exists.intro d rfl
  | e1 d =>
      right
      exact Exists.intro d rfl

theorem MetricDistanceDepth_append_left_eq_iff_empty {p d : BHist} :
    MetricDistanceDepth (append p d) = MetricDistanceDepth d ↔ hsame p BHist.Empty := by
  induction d generalizing p with
  | Empty =>
      exact MetricDistanceDepth_zero_iff_empty
  | e0 d ih =>
      constructor
      · intro sameDepth
        exact ih.mp (Nat.succ.inj sameDepth)
      · intro sameEmpty
        exact congrArg Nat.succ (ih.mpr sameEmpty)
  | e1 d ih =>
      constructor
      · intro sameDepth
        exact ih.mp (Nat.succ.inj sameDepth)
      · intro sameEmpty
        exact congrArg Nat.succ (ih.mpr sameEmpty)

theorem MetricDistanceDepth_append_right_eq_iff_empty {p d : BHist} :
    MetricDistanceDepth (append d p) = MetricDistanceDepth d ↔ hsame p BHist.Empty := by
  have depthAppend :
      ∀ x y : BHist, MetricDistanceDepth (append x y) =
        MetricDistanceDepth x + MetricDistanceDepth y := by
    intro x y
    induction y with
    | Empty =>
        rfl
    | e0 y ih =>
        exact congrArg Nat.succ ih
    | e1 y ih =>
        exact congrArg Nat.succ ih
  have addRightCancel :
      ∀ {n k m : Nat}, n + m = k + m -> n = k := by
    intro n k m same
    induction m generalizing n k with
    | zero =>
        exact same
    | succ m ih =>
        exact ih (Nat.succ.inj same)
  have addRightZeroOfEq :
      ∀ a b : Nat, a + b = a -> b = 0 := by
    intro a b same
    have swapped : b + a = 0 + a :=
      (Nat.add_comm b a).trans (same.trans (Nat.zero_add a).symm)
    exact addRightCancel swapped
  constructor
  · intro sameDepth
    have sumEq : MetricDistanceDepth d + MetricDistanceDepth p = MetricDistanceDepth d :=
      (depthAppend d p).symm.trans sameDepth
    have pZero : MetricDistanceDepth p = 0 :=
      addRightZeroOfEq (MetricDistanceDepth d) (MetricDistanceDepth p) sumEq
    exact MetricDistanceDepth_zero_iff_empty.mp pZero
  · intro sameEmpty
    cases sameEmpty
    rfl

end BEDC.Derived.MetricUp
