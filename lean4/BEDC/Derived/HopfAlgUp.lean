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

theorem HopfBialgCarrier_tensor_product_row_stability
    {tensor tensor' algebra algebra' multiplication multiplication' comultiplication
      comultiplication' : BHist} :
    TensorProductSingletonCarrier tensor ->
      RingSingletonCarrier algebra ->
        hsame tensor tensor' ->
          hsame algebra algebra' ->
            Cont tensor algebra multiplication ->
              Cont tensor' algebra' multiplication' ->
                Cont tensor algebra comultiplication ->
                  Cont tensor' algebra' comultiplication' ->
                    TensorProductSingletonCarrier tensor' ∧ hsame multiplication multiplication' ∧
                      hsame comultiplication comultiplication' := by
  intro tensorCarrier algebraCarrier sameTensor sameAlgebra multiplicationCont
    multiplicationCont' comultiplicationCont comultiplicationCont'
  have tensorEmpty : hsame tensor BHist.Empty :=
    TensorProductSingletonCarrier_empty_iff.mp tensorCarrier
  have tensorEmpty' : hsame tensor' BHist.Empty :=
    hsame_trans (hsame_symm sameTensor) tensorEmpty
  have tensorCarrier' : TensorProductSingletonCarrier tensor' :=
    TensorProductSingletonCarrier_empty_iff.mpr tensorEmpty'
  have sameMultiplication : hsame multiplication multiplication' :=
    cont_respects_hsame sameTensor sameAlgebra multiplicationCont multiplicationCont'
  have sameComultiplication : hsame comultiplication comultiplication' :=
    cont_respects_hsame sameTensor sameAlgebra comultiplicationCont comultiplicationCont'
  exact And.intro tensorCarrier'
    (And.intro sameMultiplication sameComultiplication)

theorem HopfBialgCarrier_antipode_convolution_inverse_obligation
    {tensor tensor' algebra algebra' multiplication multiplication' comultiplication comultiplication'
      antipode antipode' convLeft convLeft' endpoint endpoint' : BHist} :
    TensorProductSingletonCarrier tensor ->
      RingSingletonCarrier algebra ->
        hsame tensor tensor' ->
          hsame algebra algebra' ->
            hsame antipode antipode' ->
              Cont tensor algebra multiplication ->
                Cont tensor' algebra' multiplication' ->
                  Cont tensor algebra comultiplication ->
                    Cont tensor' algebra' comultiplication' ->
                      Cont comultiplication antipode convLeft ->
                        Cont comultiplication' antipode' convLeft' ->
                          Cont convLeft multiplication endpoint ->
                            Cont convLeft' multiplication' endpoint' ->
                              hsame multiplication multiplication' ∧
                                hsame comultiplication comultiplication' ∧
                                  hsame convLeft convLeft' ∧ hsame endpoint endpoint' := by
  intro tensorCarrier algebraCarrier sameTensor sameAlgebra sameAntipode multiplicationCont
    multiplicationCont' comultiplicationCont comultiplicationCont' convLeftCont convLeftCont'
    endpointCont endpointCont'
  have rowStability :=
    HopfBialgCarrier_tensor_product_row_stability tensorCarrier algebraCarrier sameTensor
      sameAlgebra multiplicationCont multiplicationCont' comultiplicationCont comultiplicationCont'
  have sameMultiplication : hsame multiplication multiplication' :=
    rowStability.right.left
  have sameComultiplication : hsame comultiplication comultiplication' :=
    rowStability.right.right
  have sameConvLeft : hsame convLeft convLeft' :=
    cont_respects_hsame sameComultiplication sameAntipode convLeftCont convLeftCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameConvLeft sameMultiplication endpointCont endpointCont'
  exact And.intro sameMultiplication
    (And.intro sameComultiplication
      (And.intro sameConvLeft sameEndpoint))

end BEDC.Derived.HopfAlgUp
