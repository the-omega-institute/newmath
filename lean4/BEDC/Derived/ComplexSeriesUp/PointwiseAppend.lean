import BEDC.Derived.ComplexSeriesUp

namespace BEDC.Derived.ComplexSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

theorem ComplexTermSeqCarrier_pointwise_append {c d : BHist -> BHist} :
    ComplexTermSeqCarrier c -> ComplexTermSeqCarrier d ->
      ComplexTermSeqCarrier (fun n : BHist => append (c n) (d n)) := by
  intro carrierC carrierD n unaryN
  exact ComplexHistoryCarrier_append_unary_closed (carrierC n unaryN)
    (ComplexHistoryCarrier_unary (carrierD n unaryN))

end BEDC.Derived.ComplexSeriesUp
