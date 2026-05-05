import BEDC.Derived.ComplexLimitUp.LinearClosure
import BEDC.Derived.ComplexLimitUp.PointwiseDifference

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

theorem ComplexLimit_pointwise_difference_closed {s t N M : BHist -> BHist} {z w : BHist} :
    ComplexLimit s N z M -> ComplexLimit t N w M ->
      ComplexLimit (ComplexPointwiseDifference s t) N
        (append z (append BHist.Empty w)) M := by
  intro limitS limitT
  have shiftedLimitT :
      ComplexLimit (fun n : BHist => append BHist.Empty (t n)) N
        (append BHist.Empty w) M :=
    ComplexLimit_prepend_constant_closed unary_empty limitT
  exact ComplexLimit_pointwise_append_same_modulus_closed limitS shiftedLimitT

end BEDC.Derived.ComplexLimitUp
