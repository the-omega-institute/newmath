import BEDC.FKernel.Cont

namespace BEDC.Derived.HomologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def HomologyCycleCarrier (d : BHist -> BHist) (h : BHist) : Prop :=
  hsame (d h) BHist.Empty

def HomologyBoundaryCarrier (d : BHist -> BHist) (h : BHist) : Prop :=
  Exists (fun u : BHist => hsame h (d u))

theorem HomologyCycleCarrier_append_closed {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    {h k : BHist} :
    HomologyCycleCarrier d h -> HomologyCycleCarrier d k ->
      HomologyCycleCarrier d (append h k) := by
  intro cycleH cycleK
  exact hsame_trans (dAppend h k) (by
    have dhEmpty : d h = BHist.Empty := hsame_empty_iff.mp cycleH
    have dkEmpty : d k = BHist.Empty := hsame_empty_iff.mp cycleK
    exact append_eq_empty_iff.mpr (And.intro dhEmpty dkEmpty))

theorem HomologyBoundaryCarrier_append_closed {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    {h k : BHist} :
    HomologyBoundaryCarrier d h -> HomologyBoundaryCarrier d k ->
      HomologyBoundaryCarrier d (append h k) := by
  intro boundaryH boundaryK
  cases boundaryH with
  | intro u witnessH =>
      cases boundaryK with
      | intro v witnessK =>
          have appendWitness : hsame (append h k) (append (d u) (d v)) := by
            cases witnessH
            cases witnessK
            exact hsame_refl (append (d u) (d v))
          exact Exists.intro (append u v)
            (hsame_trans appendWitness (hsame_symm (dAppend u v)))

end BEDC.Derived.HomologyUp
