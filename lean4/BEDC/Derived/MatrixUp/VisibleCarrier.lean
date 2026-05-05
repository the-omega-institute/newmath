import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Hist

theorem MatrixSingletonCarrier_visible_absurd {p : BHist} :
    (MatrixSingletonCarrier (BHist.e0 p) -> False) ∧
      (MatrixSingletonCarrier (BHist.e1 p) -> False) := by
  constructor
  · intro carrier
    exact not_hsame_e0_empty carrier
  · intro carrier
    exact not_hsame_e1_empty carrier

end BEDC.Derived.MatrixUp
