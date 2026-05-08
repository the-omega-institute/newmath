import BEDC.FKernel.Cont
import BEDC.Derived.RingUp
import BEDC.Derived.TensorProductUp

namespace BEDC.Derived.HopfAlgUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RingUp
open BEDC.Derived.TensorProductUp

def HopfAlgBialgCarrier
    (bialg tensor mul comul unit counit : BHist) : Prop :=
  RingSingletonCarrier bialg ∧ TensorProductSingletonCarrier tensor ∧
    Cont tensor mul bialg ∧ Cont tensor comul bialg ∧
      Cont unit RingSingletonOne bialg ∧ Cont counit RingSingletonOne bialg

theorem HopfAlgBialgCarrier_tensor_product_row_stability
    {bialg tensor mul comul unit counit tensor' mul' comul' : BHist} :
    HopfAlgBialgCarrier bialg tensor mul comul unit counit ->
      hsame tensor tensor' ->
      hsame mul mul' ->
      hsame comul comul' ->
      Cont tensor' mul' bialg ->
      Cont tensor' comul' bialg ->
        TensorProductSingletonCarrier tensor' ∧
          HopfAlgBialgCarrier bialg tensor' mul' comul' unit counit := by
  intro carrier sameTensor sameMul sameComul mulRow' comulRow'
  have tensorEmpty : hsame tensor BHist.Empty :=
    TensorProductSingletonCarrier_empty_iff.mp carrier.right.left
  have tensorCarrier' : TensorProductSingletonCarrier tensor' :=
    TensorProductSingletonCarrier_empty_iff.mpr
      (hsame_trans (hsame_symm sameTensor) tensorEmpty)
  have mulEndpointSame : hsame bialg bialg :=
    cont_respects_hsame sameTensor sameMul carrier.right.right.left mulRow'
  have comulEndpointSame : hsame bialg bialg :=
    cont_respects_hsame sameTensor sameComul carrier.right.right.right.left comulRow'
  have bialgCarrier : RingSingletonCarrier bialg :=
    hsame_trans mulEndpointSame (hsame_trans comulEndpointSame carrier.left)
  exact And.intro tensorCarrier'
    (And.intro bialgCarrier
      (And.intro tensorCarrier'
        (And.intro mulRow'
          (And.intro comulRow'
            (And.intro carrier.right.right.right.right.left
              carrier.right.right.right.right.right)))))

end BEDC.Derived.HopfAlgUp
