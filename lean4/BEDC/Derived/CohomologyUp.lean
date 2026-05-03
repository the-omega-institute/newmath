import BEDC.FKernel.Cont

namespace BEDC.Derived.CohomologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

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

end BEDC.Derived.CohomologyUp
