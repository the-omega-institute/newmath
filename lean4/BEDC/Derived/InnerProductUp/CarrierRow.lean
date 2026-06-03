import BEDC.Derived.InnerProductUp

namespace BEDC.Derived.InnerProductUp

open BEDC.FKernel.Hist
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp

theorem InnerProductBHistCarrierRow {x y scalarEndpoint : BHist} :
    InnerProductBHistCarrier x y scalarEndpoint ->
      VecSpaceSingletonCarrier x ∧ VecSpaceSingletonCarrier y ∧
        RealConstantHistoryClassifier scalarEndpoint (InnerProductSingletonForm x y) ∧
          hsame x BHist.Empty ∧ hsame y BHist.Empty := by
  -- BEDC touchpoint anchor: BHist hsame
  intro carrier
  exact ⟨carrier.left, carrier.right.left, carrier.right.right, carrier.left,
    carrier.right.left⟩

end BEDC.Derived.InnerProductUp
