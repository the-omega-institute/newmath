import BEDC.Derived.RatUp

namespace BEDC.Derived.ComplexAnalyticUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem ComplexAnalytic_component_continuation_witness {real imag z q zq : BHist} :
    RatHistoryCarrier real -> RatHistoryCarrier imag -> Cont real imag z -> UnaryHistory q ->
      Cont z q zq -> ∃ imagq : BHist,
        RatHistoryCarrier imagq ∧ Cont imag q imagq ∧ Cont real imagq zq ∧
          PositiveUnaryDenominator imagq := by
  intro _realCarrier imagCarrier realImag qUnary zqCont
  cases cont_assoc_middle_exists realImag zqCont with
  | intro imagq split =>
      have imagqCarrier : RatHistoryCarrier imagq :=
        RatHistoryCarrier_hsame_transport split.left.symm
          (RatHistoryCarrier_append_unary_denominator_closed imagCarrier qUnary)
      exact ⟨imagq, imagqCarrier, split.left, split.right,
        RatHistoryCarrier_iff_positive_denominator.mp imagqCarrier⟩

end BEDC.Derived.ComplexAnalyticUp
