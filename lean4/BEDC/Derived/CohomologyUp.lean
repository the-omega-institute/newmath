import BEDC.FKernel.Cont

namespace BEDC.Derived.CohomologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CohomologyCocycle_axis_right_cancel {d : BHist -> BHist} {axis h : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v))) :
    hsame (d (append h axis)) BHist.Empty -> hsame (d h) BHist.Empty := by
  intro shiftedCycle
  have shiftedByParts : hsame (append (d h) (d axis)) BHist.Empty :=
    hsame_trans (hsame_symm (dAppend h axis)) shiftedCycle
  exact (append_eq_empty_iff.mp shiftedByParts).left

theorem CohomologyCocycle_axis_left_cancel {d : BHist -> BHist} {axis h : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v))) :
    hsame (d (append axis h)) BHist.Empty -> hsame (d h) BHist.Empty := by
  intro shiftedCycle
  have shiftedByParts : hsame (append (d axis) (d h)) BHist.Empty :=
    hsame_trans (hsame_symm (dAppend axis h)) shiftedCycle
  exact (append_eq_empty_iff.mp shiftedByParts).right

theorem CohomologyCocycle_axis_context_cancel {d : BHist -> BHist} {left right h : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v))) :
    hsame (d (append left (append h right))) BHist.Empty -> hsame (d h) BHist.Empty := by
  intro contextCycle
  have rightContextCycle : hsame (d (append h right)) BHist.Empty :=
    CohomologyCocycle_axis_left_cancel dAppend contextCycle
  exact CohomologyCocycle_axis_right_cancel dAppend rightContextCycle

theorem CohomologyCocycle_axis_bilateral_cancel
    {d : BHist -> BHist} {leftAxis rightAxis h : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v))) :
    hsame (d (append (append leftAxis h) rightAxis)) BHist.Empty ->
      hsame (d h) BHist.Empty := by
  intro shiftedCycle
  have leftShiftCycle : hsame (d (append leftAxis h)) BHist.Empty :=
    CohomologyCocycle_axis_right_cancel dAppend shiftedCycle
  exact CohomologyCocycle_axis_left_cancel dAppend leftShiftCycle

theorem CohomologyCocycle_append_closed {d : BHist -> BHist} {axis h k : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (axisCycle : hsame (d axis) BHist.Empty) :
    hsame (d (append h axis)) BHist.Empty ->
      hsame (d (append k axis)) BHist.Empty ->
        hsame (d (append (append h k) axis)) BHist.Empty := by
  intro hCycle kCycle
  have dhEmpty : d h = BHist.Empty :=
    (append_eq_empty_iff.mp (hsame_trans (hsame_symm (dAppend h axis)) hCycle)).left
  have dkEmpty : d k = BHist.Empty :=
    (append_eq_empty_iff.mp (hsame_trans (hsame_symm (dAppend k axis)) kCycle)).left
  have dHKEmpty : hsame (d (append h k)) BHist.Empty :=
    hsame_trans (dAppend h k) (append_eq_empty_iff.mpr (And.intro dhEmpty dkEmpty))
  exact hsame_trans (dAppend (append h k) axis)
    (append_eq_empty_iff.mpr
      (And.intro (hsame_empty_iff.mp dHKEmpty) (hsame_empty_iff.mp axisCycle)))

theorem CohomologyCocycle_append_core_closed {d : BHist -> BHist} {h k : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v))) :
    hsame (d h) BHist.Empty -> hsame (d k) BHist.Empty ->
      hsame (d (append h k)) BHist.Empty := by
  intro hCycle kCycle
  have dhEmpty : d h = BHist.Empty :=
    hsame_empty_iff.mp hCycle
  have dkEmpty : d k = BHist.Empty :=
    hsame_empty_iff.mp kCycle
  exact hsame_trans (dAppend h k) (append_eq_empty_iff.mpr (And.intro dhEmpty dkEmpty))

theorem CohomologyCocycle_append_core_hsame_transport {d : BHist -> BHist} {h k r : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (dCongr : forall {a b : BHist}, hsame a b -> hsame (d a) (d b)) :
    hsame (d h) BHist.Empty -> hsame (d k) BHist.Empty ->
      hsame (append h k) r -> hsame (d r) BHist.Empty := by
  intro hCycle kCycle sameResult
  have appendCycle : hsame (d (append h k)) BHist.Empty :=
    CohomologyCocycle_append_core_closed dAppend hCycle kCycle
  exact hsame_trans (hsame_symm (dCongr sameResult)) appendCycle

theorem CohomologyCocycle_core_append_hsame_transport {d : BHist -> BHist} {h k r : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (dCongr : forall {a b : BHist}, hsame a b -> hsame (d a) (d b)) :
    hsame (d h) BHist.Empty -> hsame (d k) BHist.Empty ->
      hsame (append h k) r -> hsame (d r) BHist.Empty := by
  exact CohomologyCocycle_append_core_hsame_transport dAppend dCongr

theorem CohomologyCocycle_append_empty_iff {d : BHist -> BHist} {h k : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v))) :
    hsame (d (append h k)) BHist.Empty ↔
      hsame (d h) BHist.Empty ∧ hsame (d k) BHist.Empty := by
  constructor
  · intro cycle
    have splitCycle : hsame (append (d h) (d k)) BHist.Empty :=
      hsame_trans (hsame_symm (dAppend h k)) cycle
    exact append_eq_empty_iff.mp splitCycle
  · intro cycles
    exact CohomologyCocycle_append_core_closed dAppend cycles.left cycles.right

theorem CohomologyCocycle_continuation_axis_context_cancel {d : BHist -> BHist}
    {left right h k r : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v))) :
    Cont h k r -> hsame (d (append left (append r right))) BHist.Empty ->
      hsame (d h) BHist.Empty ∧ hsame (d k) BHist.Empty := by
  intro continuation contextCycle
  cases continuation
  have appendCycle : hsame (d (append h k)) BHist.Empty :=
    CohomologyCocycle_axis_context_cancel dAppend contextCycle
  exact (CohomologyCocycle_append_empty_iff (d := d) (h := h) (k := k) dAppend).mp
    appendCycle

theorem CohomologyCocycle_append_left_e1_boundary_empty_absurd
    {d : BHist -> BHist} {h k tail : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v))) :
    hsame (d h) (BHist.e1 tail) -> hsame (d (append h k)) BHist.Empty -> False := by
  intro leftVisible appendCycle
  have split : hsame (append (d h) (d k)) BHist.Empty :=
    hsame_trans (hsame_symm (dAppend h k)) appendCycle
  have leftEmpty : hsame (d h) BHist.Empty :=
    (append_eq_empty_iff.mp split).left
  exact not_hsame_e1_empty (hsame_trans (hsame_symm leftVisible) leftEmpty)

theorem CohomologyCocycle_left_shift_append_empty_iff {d : BHist -> BHist}
    {axis h k : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v))) :
    hsame (d (append axis (append h k))) BHist.Empty ↔
      hsame (d axis) BHist.Empty ∧ hsame (d h) BHist.Empty ∧ hsame (d k) BHist.Empty := by
  constructor
  · intro cycle
    have axisTail :
        hsame (d axis) BHist.Empty ∧ hsame (d (append h k)) BHist.Empty :=
      (CohomologyCocycle_append_empty_iff (d := d) (h := axis) (k := append h k)
        dAppend).mp cycle
    have tail :
        hsame (d h) BHist.Empty ∧ hsame (d k) BHist.Empty :=
      (CohomologyCocycle_append_empty_iff (d := d) (h := h) (k := k) dAppend).mp
        axisTail.right
    exact And.intro axisTail.left (And.intro tail.left tail.right)
  · intro cycles
    have tailCycle : hsame (d (append h k)) BHist.Empty :=
      (CohomologyCocycle_append_empty_iff (d := d) (h := h) (k := k) dAppend).mpr
        cycles.right
    exact (CohomologyCocycle_append_empty_iff (d := d) (h := axis) (k := append h k)
      dAppend).mpr (And.intro cycles.left tailCycle)

theorem CohomologyCocycle_axis_context_append_closed {d : BHist -> BHist}
    {left right h k : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (leftCycle : hsame (d left) BHist.Empty) (rightCycle : hsame (d right) BHist.Empty) :
    hsame (d (append left (append h right))) BHist.Empty ->
      hsame (d (append left (append k right))) BHist.Empty ->
        hsame (d (append left (append (append h k) right))) BHist.Empty := by
  intro hContextCycle kContextCycle
  have hCore : hsame (d h) BHist.Empty :=
    CohomologyCocycle_axis_context_cancel dAppend hContextCycle
  have kCore : hsame (d k) BHist.Empty :=
    CohomologyCocycle_axis_context_cancel dAppend kContextCycle
  have hkCore : hsame (d (append h k)) BHist.Empty :=
    CohomologyCocycle_append_core_closed dAppend hCore kCore
  have rightContextCycle : hsame (d (append (append h k) right)) BHist.Empty :=
    hsame_trans (dAppend (append h k) right)
      (append_eq_empty_iff.mpr
        (And.intro (hsame_empty_iff.mp hkCore) (hsame_empty_iff.mp rightCycle)))
  exact hsame_trans (dAppend left (append (append h k) right))
    (append_eq_empty_iff.mpr
      (And.intro (hsame_empty_iff.mp leftCycle) (hsame_empty_iff.mp rightContextCycle)))

theorem CohomologyCocycle_axis_context_append_hsame_transport {d : BHist -> BHist}
    {left right h k r : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (dCongr : forall {a b : BHist}, hsame a b -> hsame (d a) (d b))
    (leftCycle : hsame (d left) BHist.Empty) (rightCycle : hsame (d right) BHist.Empty) :
    hsame (d (append left (append h right))) BHist.Empty ->
      hsame (d (append left (append k right))) BHist.Empty ->
        hsame (append left (append (append h k) right)) r -> hsame (d r) BHist.Empty := by
  intro hContextCycle kContextCycle sameResult
  have contextAppendCycle :
      hsame (d (append left (append (append h k) right))) BHist.Empty :=
    CohomologyCocycle_axis_context_append_closed dAppend leftCycle rightCycle hContextCycle
      kContextCycle
  exact hsame_trans (hsame_symm (dCongr sameResult)) contextAppendCycle

theorem CohomologyCocycle_prepend_axis_closed {d : BHist -> BHist} {axis h k : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (axisCycle : hsame (d axis) BHist.Empty) :
    hsame (d (append axis h)) BHist.Empty ->
      hsame (d (append axis k)) BHist.Empty ->
        hsame (d (append axis (append h k))) BHist.Empty := by
  intro hCycle kCycle
  have dhEmpty : d h = BHist.Empty :=
    (append_eq_empty_iff.mp (hsame_trans (hsame_symm (dAppend axis h)) hCycle)).right
  have dkEmpty : d k = BHist.Empty :=
    (append_eq_empty_iff.mp (hsame_trans (hsame_symm (dAppend axis k)) kCycle)).right
  have dHKEmpty : hsame (d (append h k)) BHist.Empty :=
    hsame_trans (dAppend h k) (append_eq_empty_iff.mpr (And.intro dhEmpty dkEmpty))
  exact hsame_trans (dAppend axis (append h k))
    (append_eq_empty_iff.mpr
      (And.intro (hsame_empty_iff.mp axisCycle) (hsame_empty_iff.mp dHKEmpty)))

theorem CohomologyCocycle_left_shift_append_closed {d : BHist -> BHist} {axis h k : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (axisCycle : hsame (d axis) BHist.Empty) :
    hsame (d (append axis h)) BHist.Empty ->
      hsame (d (append axis k)) BHist.Empty ->
        hsame (d (append axis (append h k))) BHist.Empty := by
  intro hCycle kCycle
  have hCore : hsame (d h) BHist.Empty :=
    CohomologyCocycle_axis_left_cancel dAppend hCycle
  have kCore : hsame (d k) BHist.Empty :=
    CohomologyCocycle_axis_left_cancel dAppend kCycle
  have hkCore : hsame (d (append h k)) BHist.Empty :=
    CohomologyCocycle_append_core_closed dAppend hCore kCore
  exact hsame_trans (dAppend axis (append h k))
    (append_eq_empty_iff.mpr
      (And.intro (hsame_empty_iff.mp axisCycle) (hsame_empty_iff.mp hkCore)))

theorem CohomologyCocycle_append_hsame_transport {d : BHist -> BHist} {axis h k r : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (dCongr : forall {a b : BHist}, hsame a b -> hsame (d a) (d b))
    (axisCycle : hsame (d axis) BHist.Empty) :
    hsame (d (append h axis)) BHist.Empty ->
      hsame (d (append k axis)) BHist.Empty ->
        hsame (append (append h k) axis) r -> hsame (d r) BHist.Empty := by
  intro hCycle kCycle sameResult
  have appendCycle : hsame (d (append (append h k) axis)) BHist.Empty :=
    CohomologyCocycle_append_closed dAppend axisCycle hCycle kCycle
  exact hsame_trans (hsame_symm (dCongr sameResult)) appendCycle

theorem CohomologyCocycle_continuation_hsame_transport {d : BHist -> BHist}
    {h k r s : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (dCongr : forall {a b : BHist}, hsame a b -> hsame (d a) (d b)) :
    Cont h k r -> hsame (d h) BHist.Empty -> hsame (d k) BHist.Empty ->
      hsame r s -> hsame (d s) BHist.Empty := by
  intro continuation hCycle kCycle sameResult
  cases continuation
  have appendCycle : hsame (d (append h k)) BHist.Empty :=
    CohomologyCocycle_append_core_closed dAppend hCycle kCycle
  exact hsame_trans (hsame_symm (dCongr sameResult)) appendCycle

theorem CohomologyCocycle_mixed_axis_append_hsame_transport {d : BHist -> BHist}
    {axis h k r : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (dCongr : forall {a b : BHist}, hsame a b -> hsame (d a) (d b)) :
    hsame (d (append h axis)) BHist.Empty -> hsame (d (append axis k)) BHist.Empty ->
      hsame (append h k) r -> hsame (d r) BHist.Empty := by
  intro rightAxisCycle leftAxisCycle sameResult
  have hCore : hsame (d h) BHist.Empty :=
    CohomologyCocycle_axis_right_cancel dAppend rightAxisCycle
  have kCore : hsame (d k) BHist.Empty :=
    CohomologyCocycle_axis_left_cancel dAppend leftAxisCycle
  have appendCycle : hsame (d (append h k)) BHist.Empty :=
    CohomologyCocycle_append_core_closed dAppend hCore kCore
  exact hsame_trans (hsame_symm (dCongr sameResult)) appendCycle

theorem CohomologyCocycle_left_shift_append_hsame_transport {d : BHist -> BHist}
    {axis h k r : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (dCongr : forall {a b : BHist}, hsame a b -> hsame (d a) (d b))
    (axisCycle : hsame (d axis) BHist.Empty) :
    hsame (d (append axis h)) BHist.Empty ->
      hsame (d (append axis k)) BHist.Empty ->
        hsame (append axis (append h k)) r -> hsame (d r) BHist.Empty := by
  intro hCycle kCycle sameResult
  have appendCycle : hsame (d (append axis (append h k))) BHist.Empty :=
    CohomologyCocycle_left_shift_append_closed dAppend axisCycle hCycle kCycle
  exact hsame_trans (hsame_symm (dCongr sameResult)) appendCycle

theorem CohomologyCocycle_prepend_hsame_transport {d : BHist -> BHist} {axis h k r : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (dCongr : forall {a b : BHist}, hsame a b -> hsame (d a) (d b))
    (axisCycle : hsame (d axis) BHist.Empty) :
    hsame (d (append axis h)) BHist.Empty ->
      hsame (d (append axis k)) BHist.Empty ->
        hsame (append axis (append h k)) r -> hsame (d r) BHist.Empty := by
  intro hCycle kCycle sameResult
  have appendCycle : hsame (d (append axis (append h k))) BHist.Empty :=
    CohomologyCocycle_left_shift_append_closed dAppend axisCycle hCycle kCycle
  exact hsame_trans (hsame_symm (dCongr sameResult)) appendCycle

end BEDC.Derived.CohomologyUp
