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

theorem ComplexLimit_pointwise_binary_affine_combination_closed
    {a b z w : BHist} {s t N M : BHist -> BHist} :
    UnaryHistory a -> UnaryHistory b -> ComplexLimit s N z M -> ComplexLimit t N w M ->
      ComplexLimit (ComplexPointwiseBinaryAffineCombination a b s t) N
        (append (append a z) (append b w)) M := by
  intro unaryA unaryB limitS limitT
  have leftLimit :
      ComplexLimit (fun n : BHist => append a (s n)) N (append a z) M :=
    ComplexLimit_prepend_constant_closed unaryA limitS
  have rightLimit :
      ComplexLimit (fun n : BHist => append b (t n)) N (append b w) M :=
    ComplexLimit_prepend_constant_closed unaryB limitT
  exact ComplexLimit_pointwise_append_same_modulus_closed leftLimit rightLimit

theorem ComplexLimit_binary_affine_combination_closed {a b : BHist}
    {s t N M : BHist -> BHist} {z w : BHist} :
    UnaryHistory a -> UnaryHistory b -> ComplexLimit s N z M -> ComplexLimit t N w M ->
      ComplexLimit (ComplexPointwiseBinaryAffineCombination a b s t) N
        (append (append a z) (append b w)) M := by
  intro unaryA unaryB limitS limitT
  exact ComplexLimit_pointwise_append_same_modulus_closed
    (ComplexLimit_prepend_constant_closed unaryA limitS)
    (ComplexLimit_prepend_constant_closed unaryB limitT)

theorem ComplexLimit_two_sided_unary_context_closure {s N M : BHist -> BHist}
    {z p q : BHist} :
    UnaryHistory p -> UnaryHistory q -> ComplexLimit s N z M ->
      ComplexLimit (fun n : BHist => append p (append (s n) q)) N
        (append p (append z q)) M := by
  intro unaryP unaryQ limit
  have suffixed :
      ComplexLimit (fun n : BHist => append (s n) q) N (append z q) M :=
    ComplexLimit_append_constant_closed unaryQ limit
  exact ComplexLimit_prepend_constant_closed unaryP suffixed

end BEDC.Derived.ComplexLimitUp
