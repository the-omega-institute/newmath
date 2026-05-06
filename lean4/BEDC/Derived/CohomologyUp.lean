import BEDC.FKernel.Cont.Units
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CohomologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem CohomologyCocycle_semanticNameCert {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v))) :
    SemanticNameCert (fun h : BHist => hsame (d h) BHist.Empty)
      (fun h : BHist => hsame (d h) BHist.Empty)
      (fun h : BHist => hsame (d h) BHist.Empty)
      (fun h k : BHist => hsame (d h) (d k)) := by
  have emptyCycle : hsame (d BHist.Empty) BHist.Empty := by
    have idempotent : append (d BHist.Empty) (d BHist.Empty) = d BHist.Empty :=
      hsame_symm (dAppend BHist.Empty BHist.Empty)
    exact append_right_unit_iff.mp idempotent
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCycle
      equiv_refl := by
        intro h _cycle
        exact hsame_refl (d h)
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k same source
        exact hsame_trans (hsame_symm same) source
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }

theorem CohomologyCocycle_predicate_semanticNameCert {d : BHist -> BHist} {axis : BHist}
    (axisCycle : hsame (d axis) BHist.Empty)
    (dCongr : forall {a b : BHist}, hsame a b -> hsame (d a) (d b)) :
    SemanticNameCert (fun h : BHist => hsame (d h) BHist.Empty)
      (fun h : BHist => hsame (d h) BHist.Empty)
      (fun h : BHist => hsame (d h) BHist.Empty) hsame := by
  exact {
    core := {
      carrier_inhabited := Exists.intro axis axisCycle
      equiv_refl := by
        intro h _cycle
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k same source
        exact hsame_trans (hsame_symm (dCongr same)) source
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }

theorem CohomologyCocycle_hsame_transport {d : BHist -> BHist}
    (dCongr : forall {a b : BHist}, hsame a b -> hsame (d a) (d b)) {h k : BHist} :
    hsame (d h) BHist.Empty -> hsame h k -> hsame (d k) BHist.Empty := by
  intro source same
  exact hsame_trans (hsame_symm (dCongr same)) source

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

theorem CohomologyCocycle_continuation_axis_context_closed {d : BHist -> BHist}
    {left right h k r : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (dCongr : forall {a b : BHist}, hsame a b -> hsame (d a) (d b)) :
    Cont h k r -> hsame (d left) BHist.Empty -> hsame (d h) BHist.Empty ->
      hsame (d k) BHist.Empty -> hsame (d right) BHist.Empty ->
        hsame (d (append left (append r right))) BHist.Empty := by
  intro continuation leftCycle hCycle kCycle rightCycle
  have appendCycle : hsame (d (append h k)) BHist.Empty :=
    CohomologyCocycle_append_core_closed dAppend hCycle kCycle
  have rCycle : hsame (d r) BHist.Empty :=
    hsame_trans (dCongr continuation) appendCycle
  have rightContextCycle : hsame (d (append r right)) BHist.Empty :=
    CohomologyCocycle_append_core_closed dAppend rCycle rightCycle
  exact CohomologyCocycle_append_core_closed dAppend leftCycle rightContextCycle

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

theorem CohomologyCocycle_append_left_visible_boundary_empty_absurd
    {d : BHist -> BHist} {h k : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v))) :
    ((Exists fun tail : BHist => hsame (d h) (BHist.e0 tail)) \/
      (Exists fun tail : BHist => hsame (d h) (BHist.e1 tail))) ->
      hsame (d (append h k)) BHist.Empty -> False := by
  intro visible appendCycle
  have split : hsame (append (d h) (d k)) BHist.Empty :=
    hsame_trans (hsame_symm (dAppend h k)) appendCycle
  have leftEmpty : hsame (d h) BHist.Empty :=
    (append_eq_empty_iff.mp split).left
  cases visible with
  | inl e0Boundary =>
      cases e0Boundary with
      | intro tail leftVisible =>
          exact not_hsame_e0_empty (hsame_trans (hsame_symm leftVisible) leftEmpty)
  | inr e1Boundary =>
      cases e1Boundary with
      | intro tail leftVisible =>
          exact not_hsame_e1_empty (hsame_trans (hsame_symm leftVisible) leftEmpty)

theorem CohomologyCocycle_append_right_e1_boundary_empty_absurd
    {d : BHist -> BHist} {h k tail : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v))) :
    hsame (d k) (BHist.e1 tail) -> hsame (d (append h k)) BHist.Empty -> False := by
  intro rightVisible appendCycle
  have split : hsame (append (d h) (d k)) BHist.Empty :=
    hsame_trans (hsame_symm (dAppend h k)) appendCycle
  have rightEmpty : hsame (d k) BHist.Empty :=
    (append_eq_empty_iff.mp split).right
  exact not_hsame_e1_empty (hsame_trans (hsame_symm rightVisible) rightEmpty)

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

theorem CohomologyCocycle_continuation_context_cancel {d : BHist -> BHist}
    {left h mid right r : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (dCongr : forall {a b : BHist}, hsame a b -> hsame (d a) (d b)) :
    Cont left h mid -> Cont mid right r -> hsame (d r) BHist.Empty ->
      hsame (d h) BHist.Empty := by
  intro leftCont rightCont cycle
  cases leftCont
  cases rightCont
  have sameContext :
      hsame (append left (append h right)) (append (append left h) right) :=
    hsame_symm (append_assoc left h right)
  have contextCycle : hsame (d (append left (append h right))) BHist.Empty :=
    hsame_trans (dCongr sameContext) cycle
  exact CohomologyCocycle_axis_context_cancel dAppend contextCycle

theorem CohomologyCocycle_continuation_context_empty_iff {d : BHist -> BHist}
    {left h mid right r : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v))) :
    Cont left h mid -> Cont mid right r ->
      (hsame (d r) BHist.Empty <->
        hsame (d left) BHist.Empty /\ hsame (d h) BHist.Empty /\
          hsame (d right) BHist.Empty) := by
  intro leftCont rightCont
  cases leftCont
  cases rightCont
  constructor
  · intro cycle
    have outerSplit :
        hsame (d (append left h)) BHist.Empty /\ hsame (d right) BHist.Empty :=
      (CohomologyCocycle_append_empty_iff (d := d) (h := append left h) (k := right)
        dAppend).mp cycle
    have leftSplit : hsame (d left) BHist.Empty /\ hsame (d h) BHist.Empty :=
      (CohomologyCocycle_append_empty_iff (d := d) (h := left) (k := h) dAppend).mp
        outerSplit.left
    exact And.intro leftSplit.left (And.intro leftSplit.right outerSplit.right)
  · intro cycles
    have leftCycle : hsame (d (append left h)) BHist.Empty :=
      CohomologyCocycle_append_core_closed dAppend cycles.left cycles.right.left
    exact CohomologyCocycle_append_core_closed dAppend leftCycle cycles.right.right

theorem CohomologyCocycle_continuation_context_e1_boundary_empty_absurd {d : BHist -> BHist}
    {left h mid right r leftTail hTail rightTail : BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v))) :
    Cont left h mid -> Cont mid right r ->
      (hsame (d left) (BHist.e1 leftTail) ∨ hsame (d h) (BHist.e1 hTail) ∨
        hsame (d right) (BHist.e1 rightTail)) ->
        hsame (d r) BHist.Empty -> False := by
  intro leftCont rightCont visibleBoundary cycle
  have cycleParts :
      hsame (d left) BHist.Empty ∧ hsame (d h) BHist.Empty ∧
        hsame (d right) BHist.Empty :=
    (CohomologyCocycle_continuation_context_empty_iff dAppend leftCont rightCont).mp cycle
  cases visibleBoundary with
  | inl leftVisible =>
      exact not_hsame_e1_empty (hsame_trans (hsame_symm leftVisible) cycleParts.left)
  | inr rest =>
      cases rest with
      | inl hVisible =>
          exact not_hsame_e1_empty
            (hsame_trans (hsame_symm hVisible) cycleParts.right.left)
      | inr rightVisible =>
          exact not_hsame_e1_empty
            (hsame_trans (hsame_symm rightVisible) cycleParts.right.right)

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
