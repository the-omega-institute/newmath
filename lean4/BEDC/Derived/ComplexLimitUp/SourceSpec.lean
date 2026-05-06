import BEDC.Derived.ComplexLimitUp

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

def ComplexLimitSourceSpec (s N M : BHist -> BHist) (z : BHist) : Prop :=
  ComplexRegularSequence s N ∧ ComplexLimit s N z M

theorem ComplexLimitSourceSpec_constant {z : BHist} :
    ComplexHistoryCarrier z ->
      ComplexLimitSourceSpec (fun _ : BHist => z) (fun _ : BHist => BHist.Empty)
        (fun _ : BHist => BHist.Empty) z := by
  intro carrierZ
  have zUnary : UnaryHistory z := ComplexHistoryCarrier_unary carrierZ
  exact And.intro (ComplexRegularSequence_constant zUnary) (ComplexLimit_constant carrierZ)

end BEDC.Derived.ComplexLimitUp
