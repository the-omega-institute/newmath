import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem MatrixSingletonAddMul_visible_right_continuation_result_nonempty {M n R : BHist} :
    (Cont (MatrixSingletonAdd M (BHist.e0 n)) (MatrixSingletonMul M (BHist.e0 n)) R ->
      hsame R BHist.Empty -> False) ∧
    (Cont (MatrixSingletonAdd M (BHist.e1 n)) (MatrixSingletonMul M (BHist.e1 n)) R ->
      hsame R BHist.Empty -> False) := by
  constructor
  · intro continuation resultEmpty
    have emptyFactors :=
      Iff.mp (MatrixSingletonAddMul_continuation_empty_result_factors_iff continuation)
        resultEmpty
    exact not_hsame_e0_empty emptyFactors.right
  · intro continuation resultEmpty
    have emptyFactors :=
      Iff.mp (MatrixSingletonAddMul_continuation_empty_result_factors_iff continuation)
        resultEmpty
    exact not_hsame_e1_empty emptyFactors.right

end BEDC.Derived.MatrixUp
