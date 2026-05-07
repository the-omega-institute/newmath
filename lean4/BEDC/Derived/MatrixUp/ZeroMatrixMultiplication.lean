import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem MatrixFiniteFoldZeroMatrix_multiplication_law {A B left right : BHist} :
    MatrixSingletonCarrier A -> MatrixSingletonCarrier B -> Cont MatrixSingletonZero B left ->
      Cont A MatrixSingletonZero right ->
        MatrixSingletonCarrier left ∧ MatrixSingletonCarrier right ∧
          MatrixSingletonClassifier left MatrixSingletonZero ∧
            MatrixSingletonClassifier right MatrixSingletonZero ∧
              MatrixSingletonClassifier left right := by
  intro carrierA carrierB leftRow rightRow
  have zeroCarrier : MatrixSingletonCarrier MatrixSingletonZero := hsame_refl BHist.Empty
  have leftCarrier : MatrixSingletonCarrier left :=
    cont_respects_hsame zeroCarrier carrierB leftRow (cont_right_unit BHist.Empty)
  have rightCarrier : MatrixSingletonCarrier right :=
    cont_respects_hsame carrierA zeroCarrier rightRow (cont_right_unit BHist.Empty)
  have leftClassified : MatrixSingletonClassifier left MatrixSingletonZero :=
    ⟨leftCarrier, zeroCarrier, hsame_trans leftCarrier (hsame_symm zeroCarrier)⟩
  have rightClassified : MatrixSingletonClassifier right MatrixSingletonZero :=
    ⟨rightCarrier, zeroCarrier, hsame_trans rightCarrier (hsame_symm zeroCarrier)⟩
  have endpointsClassified : MatrixSingletonClassifier left right :=
    ⟨leftCarrier, rightCarrier, hsame_trans leftCarrier (hsame_symm rightCarrier)⟩
  exact ⟨leftCarrier, rightCarrier, leftClassified, rightClassified, endpointsClassified⟩

end BEDC.Derived.MatrixUp
