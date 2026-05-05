import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem MatrixSingletonCarrier_continuation_result_iff {M N R : BHist} :
    MatrixSingletonCarrier M ->
      MatrixSingletonCarrier N -> (Cont M N R ↔ MatrixSingletonCarrier R) := by
  intro carrierM carrierN
  constructor
  · intro continuation
    cases carrierM
    cases carrierN
    exact cont_deterministic continuation (cont_right_unit BHist.Empty)
  · intro carrierR
    cases carrierM
    cases carrierN
    cases carrierR
    exact cont_right_unit BHist.Empty

end BEDC.Derived.MatrixUp
