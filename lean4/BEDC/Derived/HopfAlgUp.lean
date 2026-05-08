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

end BEDC.Derived.HopfAlgUp
