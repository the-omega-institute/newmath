import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem MatrixSingletonPow_positive_tail_empty_continuation_factors {M depth tail y r : BHist} :
    UnaryHistory depth -> depth = BHist.e1 tail ->
      Cont (MatrixSingletonPow M depth) y r -> hsame r BHist.Empty ->
        MatrixSingletonCarrier (MatrixSingletonPow M tail) ∧
          MatrixSingletonCarrier M ∧ MatrixSingletonCarrier y := by
  intro _depthUnary depthEq continuation resultEmpty
  cases depthEq
  have emptyContinuation : Cont (MatrixSingletonPow M (BHist.e1 tail)) y BHist.Empty :=
    cont_result_hsame_transport continuation resultEmpty
  have continuationParts := cont_empty_result_inversion emptyContinuation
  have sourceParts :
      MatrixSingletonCarrier (MatrixSingletonPow M tail) ∧ MatrixSingletonCarrier M :=
    append_eq_empty_iff.mp continuationParts.left
  exact And.intro sourceParts.left (And.intro sourceParts.right continuationParts.right)

end BEDC.Derived.MatrixUp
