import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.NameCert
import BEDC.Derived.RingUp
import BEDC.Derived.TensorProductUp

namespace BEDC.Derived.HopfAlgUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.RingUp
open BEDC.Derived.TensorProductUp

def HopfAlgBialgCarrier
    (bialg tensor mul comul unit counit : BHist) : Prop :=
  RingSingletonCarrier bialg ∧ TensorProductSingletonCarrier tensor ∧
    Cont tensor mul bialg ∧ Cont tensor comul bialg ∧
      Cont unit RingSingletonOne bialg ∧ Cont counit RingSingletonOne bialg

def HopfAlgAntipodeClassifier
    (bialg tensor antipode unit counit bialg' tensor' antipode' unit' counit' : BHist) :
    Prop :=
  hsame bialg bialg' ∧ hsame tensor tensor' ∧ hsame antipode antipode' ∧
    hsame unit unit' ∧ hsame counit counit'

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

theorem HopfAlgBialgCarrier_namecert_obligation_surface
    {bialg tensor mul comul unit counit : BHist} :
    HopfAlgBialgCarrier bialg tensor mul comul unit counit ->
      SemanticNameCert
          (fun endpoint : BHist =>
            exists t m c u e : BHist, HopfAlgBialgCarrier endpoint t m c u e)
          (fun endpoint : BHist =>
            exists t m c u e : BHist, HopfAlgBialgCarrier endpoint t m c u e)
          (fun endpoint : BHist =>
            exists t m c u e : BHist, HopfAlgBialgCarrier endpoint t m c u e)
          (fun left right : BHist =>
            (exists lt lm lc lu le : BHist, HopfAlgBialgCarrier left lt lm lc lu le) ∧
            (exists rt rm rc ru re : BHist, HopfAlgBialgCarrier right rt rm rc ru re) ∧
              hsame left right) ∧
        Cont tensor mul bialg ∧ Cont tensor comul bialg := by
  intro carrier
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          refine Exists.intro bialg ?_
          refine Exists.intro tensor ?_
          refine Exists.intro mul ?_
          refine Exists.intro comul ?_
          refine Exists.intro unit ?_
          exact Exists.intro counit carrier
        equiv_refl := by
          intro endpoint source
          exact And.intro source (And.intro source (hsame_refl endpoint))
        equiv_symm := by
          intro left right same
          exact And.intro same.right.left
            (And.intro same.left (hsame_symm same.right.right))
        equiv_trans := by
          intro left middle right sameLeftMiddle sameMiddleRight
          exact And.intro sameLeftMiddle.left
            (And.intro sameMiddleRight.right.left
              (hsame_trans sameLeftMiddle.right.right sameMiddleRight.right.right))
        carrier_respects_equiv := by
          intro left right same _source
          exact same.right.left
      }
      pattern_sound := by
        intro endpoint source
        exact source
      ledger_sound := by
        intro endpoint source
        exact source
    }
  · exact And.intro carrier.right.right.left carrier.right.right.right.left

theorem HopfAlgBialgCarrier_antipode_convolution_inverse_unique
    {bialg tensor mul comul unit counit antipode antipode' left left' endpoint endpoint' :
      BHist} :
    HopfAlgBialgCarrier bialg tensor mul comul unit counit ->
      Cont comul antipode left ->
        Cont left mul endpoint ->
          Cont comul antipode' left' ->
            Cont left' mul endpoint' ->
              Cont unit counit endpoint ->
                Cont unit counit endpoint' -> hsame antipode antipode' := by
  intro _carrier leftRow endpointRow leftRow' endpointRow' unitEndpoint unitEndpoint'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_deterministic unitEndpoint unitEndpoint'
  exact cont_cancel_common_context leftRow endpointRow leftRow' endpointRow' sameEndpoint

theorem HopfAlgAntipodeClassifier_convolution_inverse_unique
    {bialg tensor mul comul unit counit antipode antipode' left left' endpoint endpoint' :
      BHist} :
    HopfAlgBialgCarrier bialg tensor mul comul unit counit ->
      Cont comul antipode left ->
        Cont left mul endpoint ->
          Cont comul antipode' left' ->
            Cont left' mul endpoint' ->
              hsame endpoint endpoint' ->
                HopfAlgAntipodeClassifier bialg tensor antipode unit counit bialg tensor
                  antipode' unit counit := by
  intro carrier leftConv leftEndpoint rightConv rightEndpoint sameEndpoint
  have sameAntipode : hsame antipode antipode' :=
    cont_cancel_common_context leftConv leftEndpoint rightConv rightEndpoint sameEndpoint
  have sameBialg : hsame bialg bialg :=
    hsame_trans carrier.left (hsame_symm carrier.left)
  have tensorEmpty : hsame tensor BHist.Empty :=
    TensorProductSingletonCarrier_empty_iff.mp carrier.right.left
  have sameTensor : hsame tensor tensor :=
    hsame_trans tensorEmpty (hsame_symm tensorEmpty)
  have sameUnit : hsame unit unit :=
    cont_right_cancel carrier.right.right.right.right.left
      carrier.right.right.right.right.left
  have sameCounit : hsame counit counit :=
    cont_right_cancel carrier.right.right.right.right.right
      carrier.right.right.right.right.right
  exact And.intro sameBialg
    (And.intro sameTensor
      (And.intro sameAntipode (And.intro sameUnit sameCounit)))

theorem HopfAlgAntipodeClassifier_transport
    {bialg tensor mul comul unit counit bialg' tensor' mul' comul' unit' counit'
      antipode antipode' left left' endpoint endpoint' : BHist} :
    hsame bialg bialg' ->
      hsame tensor tensor' ->
        hsame unit unit' ->
          hsame counit counit' ->
            hsame comul comul' ->
              hsame mul mul' ->
                Cont comul antipode left ->
                  Cont left mul endpoint ->
                    Cont comul' antipode' left' ->
                      Cont left' mul' endpoint' ->
                        hsame endpoint endpoint' ->
                          HopfAlgAntipodeClassifier bialg tensor antipode unit counit bialg'
                            tensor' antipode' unit' counit' := by
  intro sameBialg sameTensor sameUnit sameCounit sameComul sameMul leftConv leftEndpoint
    rightConv rightEndpoint sameEndpoint
  have sameLeft : hsame left left' :=
    cont_cancel_hsame_right_context leftEndpoint rightEndpoint sameMul sameEndpoint
  have sameAntipode : hsame antipode antipode' :=
    cont_cancel_hsame_left_context leftConv rightConv sameComul sameLeft
  exact And.intro sameBialg
    (And.intro sameTensor
      (And.intro sameAntipode (And.intro sameUnit sameCounit)))

end BEDC.Derived.HopfAlgUp
