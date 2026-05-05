import BEDC.Derived.ComplexLimitUp

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

def ComplexPointwiseNegation (s : BHist -> BHist) (n : BHist) : BHist :=
  append BHist.Empty (s n)

theorem ComplexLimit_pointwise_negation {s N M : BHist -> BHist} {z : BHist} :
    ComplexLimit s N z M ->
      ComplexLimit (fun n : BHist => append BHist.Empty (s n)) N
        (append BHist.Empty z) M := by
  intro limit
  cases limit with
  | intro regular rest =>
      cases rest with
      | intro carrierZ modulus =>
          exact And.intro
            (ComplexRegularSequence_prepend_constant_closed unary_empty regular)
            (And.intro (ComplexHistoryCarrier_prepend_unary_closed unary_empty carrierZ)
              (fun k n unaryK unaryN controlled =>
                match modulus k n unaryK unaryN controlled with
                | Exists.intro d distance =>
                    Exists.intro (append (append BHist.Empty (s n)) (append BHist.Empty z))
                      (ComplexDistance_prepend_constant_closed unary_empty distance)))

end BEDC.Derived.ComplexLimitUp
