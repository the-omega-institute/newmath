import BEDC.FKernel.Hist

namespace BEDC.Derived.EmptyUp

open BEDC.FKernel.Hist

def EmptyHistoryCarrier (h : BHist) : Prop :=
  hsame h (BHist.e0 BHist.Empty) ∧ hsame h (BHist.e1 BHist.Empty)

theorem EmptyHistoryCarrier_absurd {h : BHist} :
    EmptyHistoryCarrier h -> False := by
  intro carrier
  cases carrier.left
  cases carrier.right

end BEDC.Derived.EmptyUp
