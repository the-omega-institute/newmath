import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ComplexUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ProdUp
open BEDC.Derived.RatUp

theorem ComplexHistoryCarrier_unary_continuation_closed {h q zq : BHist} :
    ComplexHistoryCarrier h -> UnaryHistory q -> Cont h q zq -> ComplexHistoryCarrier zq := by
  intro carrier qUnary suffixCont
  cases carrier with
  | intro real rest =>
      cases rest with
      | intro imag data =>
          cases data with
          | intro realCarrier rest =>
              cases rest with
              | intro imagCarrier componentCont =>
                  cases cont_assoc_middle_exists componentCont suffixCont with
                  | intro imagq split =>
                      have imagqCarrier : RatHistoryCarrier imagq :=
                        RatHistoryCarrier_hsame_transport split.left.symm
                          (RatHistoryCarrier_append_unary_denominator_closed imagCarrier qUnary)
                      exact ProdHistoryCarrier_cont_intro realCarrier imagqCarrier split.right

theorem ComplexHistoryClassifier_unary_continuation_closed {h k q q' zq wq : BHist} :
    ComplexHistoryClassifier h k -> UnaryHistory q -> hsame q q' -> Cont h q zq ->
      Cont k q' wq -> ComplexHistoryClassifier zq wq := by
  intro classified qUnary sameQQ' leftCont rightCont
  have qUnary' : UnaryHistory q' := unary_transport qUnary sameQQ'
  have carrierZq : ComplexHistoryCarrier zq :=
    ComplexHistoryCarrier_unary_continuation_closed classified.left qUnary leftCont
  have carrierWq : ComplexHistoryCarrier wq :=
    ComplexHistoryCarrier_unary_continuation_closed classified.right.left qUnary' rightCont
  have sameResults : hsame zq wq :=
    cont_respects_hsame classified.right.right sameQQ' leftCont rightCont
  exact ⟨carrierZq, carrierWq, sameResults⟩

end BEDC.Derived.ComplexUp
