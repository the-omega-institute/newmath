import BEDC.Derived.ComplexLimitUp

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

theorem ComplexLimit_stability_certificate_fields :
    (forall {s N M : BHist -> BHist} {z z' : BHist}, hsame z z' ->
      ComplexLimit s N z M -> ComplexLimit s N z' M) ∧
    (forall {s t N : BHist -> BHist},
      (forall {n : BHist}, UnaryHistory n -> hsame (s n) (t n)) ->
        ComplexRegularSequence s N -> ComplexRegularSequence t N) ∧
    (forall {s t N M : BHist -> BHist} {z : BHist},
      (forall {n : BHist}, UnaryHistory n -> hsame (s n) (t n)) ->
        ComplexLimit s N z M -> ComplexLimit t N z M) := by
  constructor
  · intro s N M z z' sameZ limit
    exact ComplexLimit_hsame_transport sameZ limit
  · constructor
    · intro s t N pointwise regular
      exact ComplexRegularSequence_hsame_transport pointwise regular
    · intro s t N M z pointwise limit
      exact ComplexLimit_sequence_hsame_transport pointwise limit

end BEDC.Derived.ComplexLimitUp
