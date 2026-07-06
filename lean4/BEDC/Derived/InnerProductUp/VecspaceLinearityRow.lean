import BEDC.Derived.InnerProductUp

namespace BEDC.Derived.InnerProductUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp

theorem InnerProductVecspaceLinearityRow {x y x' y' combined : BHist} :
    VecSpaceSingletonCarrier x ->
      VecSpaceSingletonCarrier y ->
        VecSpaceSingletonClassifier x x' ->
          VecSpaceSingletonClassifier y y' ->
            Cont (InnerProductSingletonForm x y) (InnerProductSingletonForm x' y') combined ->
              RealConstantHistoryClassifier (InnerProductSingletonForm x y)
                  (BHist.e1 (BHist.e1 BHist.Empty)) ∧
                RealConstantHistoryClassifier (InnerProductSingletonForm x' y')
                  (BHist.e1 (BHist.e1 BHist.Empty)) ∧
                  UnaryHistory combined ∧
                    hsame combined
                      (append (InnerProductSingletonForm x y)
                        (InnerProductSingletonForm x' y')) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrierX carrierY classifiedXX' classifiedYY' combinedRoute
  have targetCarrierX : VecSpaceSingletonCarrier x' := classifiedXX'.right.left
  have targetCarrierY : VecSpaceSingletonCarrier y' := classifiedYY'.right.left
  have sourceExposure := InnerProductRoot_vecspace_scalar_exposure carrierX carrierY
  have targetExposure := InnerProductRoot_vecspace_scalar_exposure targetCarrierX targetCarrierY
  have sourceUnary : UnaryHistory (InnerProductSingletonForm x y) := by
    unfold InnerProductSingletonForm
    exact unary_e1_closed (unary_e1_closed unary_empty)
  have targetUnary : UnaryHistory (InnerProductSingletonForm x' y') := by
    unfold InnerProductSingletonForm
    exact unary_e1_closed (unary_e1_closed unary_empty)
  have combinedUnary : UnaryHistory combined :=
    unary_cont_closed sourceUnary targetUnary combinedRoute
  exact ⟨sourceExposure.right.right, targetExposure.right.right, combinedUnary, combinedRoute⟩

end BEDC.Derived.InnerProductUp
