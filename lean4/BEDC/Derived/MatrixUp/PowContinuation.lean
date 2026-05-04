import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem MatrixSingletonPow_positive_exponent_empty_continuation_base_carrier {M exponent y r : BHist} :
    UnaryHistory exponent -> (hsame exponent BHist.Empty -> False) ->
      Cont (MatrixSingletonPow M exponent) y r -> hsame r BHist.Empty ->
        MatrixSingletonCarrier M := by
  intro exponentUnary exponentNonempty continuation resultEmpty
  have emptyContinuation : Cont (MatrixSingletonPow M exponent) y BHist.Empty :=
    cont_result_hsame_transport continuation resultEmpty
  have powCarrier : MatrixSingletonCarrier (MatrixSingletonPow M exponent) :=
    (cont_empty_result_inversion emptyContinuation).left
  exact (MatrixSingletonPow_carrier_nonempty_unary_input_iff exponentUnary exponentNonempty).mp
    powCarrier

end BEDC.Derived.MatrixUp
