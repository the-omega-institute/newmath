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

end BEDC.Derived.CohomologyUp
