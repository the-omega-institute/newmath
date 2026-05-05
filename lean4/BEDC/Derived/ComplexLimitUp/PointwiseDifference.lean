import BEDC.Derived.ComplexLimitUp
import BEDC.Derived.ComplexLimitUp.PointwiseNegation

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def ComplexPointwiseDifference (s t : BHist -> BHist) (n : BHist) : BHist :=
  append (s n) (append BHist.Empty (t n))

theorem ComplexLimit_pointwise_difference {s t N M : BHist -> BHist} {z w : BHist} :
    ComplexLimit s N z M -> ComplexLimit t N w M ->
      ComplexLimit (fun n : BHist => append (s n) (append BHist.Empty (t n))) N
        (append z (append BHist.Empty w)) M := by
  intro limitS limitT
  exact ComplexLimit_pointwise_append_same_modulus_closed limitS
    (ComplexLimit_pointwise_negation limitT)

end BEDC.Derived.ComplexLimitUp
