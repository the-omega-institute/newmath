import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem MatrixUp_StdBridge {M N R : BHist} :
    MatrixSingletonCarrier M ->
      MatrixSingletonCarrier N ->
        Cont (MatrixSingletonAdd M N) (MatrixSingletonMul M N) R ->
          SemanticNameCert MatrixSingletonCarrier MatrixSingletonCarrier
              MatrixSingletonCarrier MatrixSingletonClassifier ∧
            MatrixSingletonCarrier R ∧ hsame R BHist.Empty ∧
              MatrixSingletonClassifier MatrixSingletonZero BHist.Empty ∧
                MatrixSingletonClassifier MatrixSingletonOne BHist.Empty := by
  intro carrierM carrierN continuation
  have laws := MatrixSingletonEmptyHistory_laws
  have cert :
      SemanticNameCert MatrixSingletonCarrier MatrixSingletonCarrier MatrixSingletonCarrier
          MatrixSingletonClassifier :=
    laws.left
  have zeroClassified : MatrixSingletonClassifier MatrixSingletonZero BHist.Empty := by
    exact And.intro laws.right.left
      (And.intro (hsame_refl BHist.Empty) laws.right.left)
  have oneClassified : MatrixSingletonClassifier MatrixSingletonOne BHist.Empty := by
    exact And.intro laws.right.right.left
      (And.intro (hsame_refl BHist.Empty) laws.right.right.left)
  have endpointExact := MatrixSingletonEmptyHistory_endpoint_exactness carrierM carrierN
  have addCarrier : MatrixSingletonCarrier (MatrixSingletonAdd M N) :=
    endpointExact.right.right.right.left.left
  have mulCarrier : MatrixSingletonCarrier (MatrixSingletonMul M N) :=
    endpointExact.right.right.right.right.left
  have resultCarrier : MatrixSingletonCarrier R := by
    cases continuation
    exact append_eq_empty_iff.mpr (And.intro addCarrier mulCarrier)
  exact ⟨cert, resultCarrier, resultCarrier, zeroClassified, oneClassified⟩

end BEDC.Derived.MatrixUp
