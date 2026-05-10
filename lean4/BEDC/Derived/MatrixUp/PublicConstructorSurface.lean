import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem MatrixSingletonEmptyHistory_public_constructor_surface {M N : BHist} :
    MatrixSingletonCarrier M ->
      MatrixSingletonCarrier N ->
        MatrixSingletonCarrier MatrixSingletonZero ∧
          MatrixSingletonCarrier MatrixSingletonOne ∧
            MatrixSingletonCarrier (MatrixSingletonAdd M N) ∧
              MatrixSingletonCarrier (MatrixSingletonMul M N) ∧
                MatrixSingletonClassifier (MatrixSingletonAdd M N) BHist.Empty ∧
                  MatrixSingletonClassifier (MatrixSingletonMul M N) BHist.Empty := by
  intro carrierM carrierN
  have laws := MatrixSingletonEmptyHistory_laws
  have zeroCarrier : MatrixSingletonCarrier MatrixSingletonZero :=
    laws.right.left
  have oneCarrier : MatrixSingletonCarrier MatrixSingletonOne :=
    laws.right.right.left
  have operationCarriers :=
    laws.right.right.right.left carrierM carrierN
  have emptyCarrier : MatrixSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have addClassifier :
      MatrixSingletonClassifier (MatrixSingletonAdd M N) BHist.Empty :=
    And.intro operationCarriers.left
      (And.intro emptyCarrier operationCarriers.left)
  have mulClassifier :
      MatrixSingletonClassifier (MatrixSingletonMul M N) BHist.Empty :=
    And.intro operationCarriers.right
      (And.intro emptyCarrier operationCarriers.right)
  exact
    ⟨zeroCarrier, oneCarrier, operationCarriers.left, operationCarriers.right, addClassifier,
      mulClassifier⟩

end BEDC.Derived.MatrixUp
