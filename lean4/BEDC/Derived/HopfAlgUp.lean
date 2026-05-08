import BEDC.Derived.RingUp
import BEDC.Derived.TensorProductUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.HopfAlgUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RingUp
open BEDC.Derived.TensorProductUp

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
