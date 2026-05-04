import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingletonCarrier_append_context_empty_iff {L R h : BHist} :
    GroupSingletonCarrier L -> GroupSingletonCarrier R ->
      (GroupSingletonCarrier (append L (append h R)) <-> GroupSingletonCarrier h) := by
  intro carrierL carrierR
  constructor
  · intro contextualCarrier
    have outerSplit := append_eq_empty_iff.mp contextualCarrier
    exact (append_eq_empty_iff.mp outerSplit.right).left
  · intro carrierH
    exact append_eq_empty_iff.mpr
      (And.intro carrierL (append_eq_empty_iff.mpr (And.intro carrierH carrierR)))

end BEDC.Derived.GroupUp
