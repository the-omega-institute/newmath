import BEDC.Derived.PrimeUp

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

end BEDC.Derived.PrimeUp
