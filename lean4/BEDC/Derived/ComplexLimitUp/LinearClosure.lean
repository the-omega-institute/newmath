import BEDC.Derived.ComplexLimitUp

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

def ComplexPointwiseBinaryAffineCombination (a b : BHist) (s t : BHist -> BHist)
    (n : BHist) : BHist :=
  append (append a (s n)) (append b (t n))

theorem ComplexLimit_prepend_constant_closed {s N M : BHist -> BHist} {z q : BHist} :
    UnaryHistory q -> ComplexLimit s N z M ->
      ComplexLimit (fun n : BHist => append q (s n)) N (append q z) M := by
  intro unaryQ limit
  cases limit with
  | intro regular rest =>
      cases rest with
      | intro carrierZ modulus =>
          exact And.intro (ComplexRegularSequence_prepend_constant_closed unaryQ regular)
            (And.intro (ComplexHistoryCarrier_prepend_unary_closed unaryQ carrierZ)
              (fun k n unaryK unaryN controlled =>
                match modulus k n unaryK unaryN controlled with
                | Exists.intro d distance =>
                    Exists.intro (append (append q (s n)) (append q z))
                      (ComplexDistance_prepend_constant_closed unaryQ distance)))

end BEDC.Derived.ComplexLimitUp
