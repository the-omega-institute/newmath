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

theorem MatrixSingletonPow_positive_exponent_continuation_result_carrier_iff {M exponent y r : BHist} :
    UnaryHistory exponent -> (hsame exponent BHist.Empty -> False) ->
      Cont (MatrixSingletonPow M exponent) y r ->
        (MatrixSingletonCarrier r ↔ MatrixSingletonCarrier M ∧ MatrixSingletonCarrier y) := by
  intro exponentUnary exponentNonempty continuation
  constructor
  · intro resultCarrier
    have emptyContinuation : Cont (MatrixSingletonPow M exponent) y BHist.Empty :=
      cont_result_hsame_transport continuation resultCarrier
    have emptyParts := cont_empty_result_inversion emptyContinuation
    have baseCarrier : MatrixSingletonCarrier M :=
      (MatrixSingletonPow_carrier_nonempty_unary_input_iff exponentUnary exponentNonempty).mp
        emptyParts.left
    exact And.intro baseCarrier emptyParts.right
  · intro carrierData
    have powCarrier : MatrixSingletonCarrier (MatrixSingletonPow M exponent) :=
      (MatrixSingletonPow_carrier_nonempty_unary_input_iff exponentUnary exponentNonempty).mpr
        carrierData.left
    have appendEmpty : hsame (append (MatrixSingletonPow M exponent) y) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro powCarrier carrierData.right)
    exact continuation.trans appendEmpty

end BEDC.Derived.MatrixUp
