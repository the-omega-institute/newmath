import BEDC.Derived.ComplexLimitUp

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

theorem ComplexLimit_constant_of_regular {z : BHist}
    (regular : ComplexRegularSequence (fun _ : BHist => z) (fun _ : BHist => BHist.Empty)) :
    ComplexHistoryCarrier z ->
      ComplexLimit (fun _ : BHist => z) (fun _ : BHist => BHist.Empty) z
        (fun _ : BHist => BHist.Empty) := by
  intro carrierZ
  have zUnary : UnaryHistory z := ComplexHistoryCarrier_unary carrierZ
  exact And.intro regular
    (And.intro carrierZ
      (fun k n unaryK unaryN controlled =>
        Exists.intro (append z z)
          (And.intro zUnary
            (And.intro zUnary
              (And.intro (unary_append_closed zUnary zUnary) (Or.inl (cont_intro rfl)))))))

end BEDC.Derived.ComplexLimitUp
