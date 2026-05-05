import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem MatrixSingletonMulContinuation_result_carrier_iff {M N h r : BHist} :
    Cont h (MatrixSingletonMul M N) r ->
      (MatrixSingletonCarrier r ↔
        MatrixSingletonCarrier h ∧ MatrixSingletonCarrier M ∧ MatrixSingletonCarrier N) := by
  intro continuation
  constructor
  · intro resultCarrier
    have emptyContinuation : Cont h (MatrixSingletonMul M N) BHist.Empty :=
      cont_result_hsame_transport continuation resultCarrier
    have endpoints := cont_empty_result_inversion emptyContinuation
    have factors := append_eq_empty_iff.mp endpoints.right
    exact ⟨endpoints.left, factors.left, factors.right⟩
  · intro carriers
    have targetCarrier : MatrixSingletonCarrier (MatrixSingletonMul M N) :=
      append_eq_empty_iff.mpr ⟨carriers.right.left, carriers.right.right⟩
    exact
      cont_respects_hsame carriers.left targetCarrier continuation (cont_right_unit BHist.Empty)

end BEDC.Derived.MatrixUp
