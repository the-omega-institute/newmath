import BEDC.Derived.PrimeUp
import BEDC.Derived.PrimeUp.ZeroHeadedComponent

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem NatMul_succ_result_positive_shape {d q n : BHist} :
    NatMul d (BHist.e1 q) n -> (hsame d BHist.Empty -> False) ->
      exists r : BHist, hsame n (BHist.e1 r) ∧ UnaryHistory r := by
  intro mul dNonempty
  have dCarrier : UnaryHistory d := NatMul_left_unary mul
  have stepData := NatMul_succ_inversion mul
  cases stepData with
  | intro previous data =>
      cases d with
      | Empty =>
          exact False.elim (dNonempty (hsame_refl BHist.Empty))
      | e0 tail =>
          cases dCarrier
      | e1 tail =>
          have previousCarrier : UnaryHistory previous :=
            NatMul_result_unary dCarrier data.left
          exact ⟨append previous tail, data.right,
            unary_append_closed previousCarrier (unary_e1_inversion dCarrier)⟩

theorem NatMul_nonempty_multiplier_result_positive_shape {d q n : BHist} :
    NatMul d q n -> (hsame q BHist.Empty -> False) -> (hsame d BHist.Empty -> False) ->
      exists tail : BHist, hsame n (BHist.e1 tail) ∧ UnaryHistory tail := by
  intro mul qNonempty dNonempty
  cases q with
  | Empty =>
      exact False.elim (qNonempty (hsame_refl BHist.Empty))
  | e0 qTail =>
      have qUnary : UnaryHistory (BHist.e0 qTail) := NatMul_right_unary mul
      cases qUnary
  | e1 qTail =>
      exact NatMul_succ_result_positive_shape mul dNonempty

theorem NatMul_successor_result_multiplier_positive_shape {d q n : BHist} :
    NatMul d q (BHist.e1 n) -> exists tail : BHist, hsame q (BHist.e1 tail) ∧
      UnaryHistory tail := by
  intro mul
  have qUnary : UnaryHistory q := NatMul_right_unary mul
  cases q with
  | Empty => cases mul
  | e0 _tail => cases qUnary
  | e1 tail => exact ⟨tail, hsame_refl (BHist.e1 tail), unary_e1_inversion qUnary⟩

theorem NatFact_successor_result_positive_shape {n m : BHist} :
    NatFact (BHist.e1 n) m -> exists tail : BHist, hsame m (BHist.e1 tail) ∧
      UnaryHistory tail := by
  intro fact
  have stepData := NatFact_successor_inversion fact
  cases stepData with
  | intro previous data =>
      exact NatMul_nonempty_multiplier_result_positive_shape data.right
        (NatFact_result_not_empty data.left) not_hsame_e1_empty

end BEDC.Derived.PrimeUp
