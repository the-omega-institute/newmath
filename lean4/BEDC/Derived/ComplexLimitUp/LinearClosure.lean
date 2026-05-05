import BEDC.Derived.ComplexLimitUp

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

def ComplexPointwiseBinaryAffineCombination (a b : BHist) (s t : BHist -> BHist)
    (n : BHist) : BHist :=
  append (append a (s n)) (append b (t n))

def ComplexPointwiseDifference (s t : BHist -> BHist) (n : BHist) : BHist :=
  append (s n) (append BHist.Empty (t n))

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

theorem ComplexLimit_pointwise_negation_closed {s N M : BHist -> BHist} {z : BHist} :
    ComplexLimit s N z M ->
      ComplexLimit (fun n : BHist => append BHist.Empty (s n)) N
        (append BHist.Empty z) M := by
  intro limit
  have shiftedLimit :
    ComplexLimit (fun n : BHist => append BHist.Empty (s n)) N z M :=
    ComplexLimit_sequence_hsame_transport
      (fun {n : BHist} _unaryN => hsame_symm (append_empty_left (s n))) limit
  exact ComplexLimit_hsame_transport (hsame_symm (append_empty_left z)) shiftedLimit

end BEDC.Derived.ComplexLimitUp
