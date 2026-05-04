import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem NatDivides_cont_closed {d x y z : BHist} :
    NatDivides d x → NatDivides d y → Cont x y z → NatDivides d z := by
  intro dividesX dividesY continuation
  cases dividesX with
  | intro qx qxData =>
      cases qxData with
      | intro qxUnary qxMul =>
          cases dividesY with
          | intro qy qyData =>
              cases qyData with
              | intro qyUnary qyMul =>
                  exact Exists.intro (append qx qy)
                    (And.intro (unary_append_closed qxUnary qyUnary)
                      (NatMul_append_cont qxMul qyMul continuation))

theorem NatMul_append_multiplier_total {d w n q : BHist} :
    NatMul d w n -> UnaryHistory q ->
      ∃ r : BHist, UnaryHistory r ∧ NatMul d (append w q) r := by
  intro mul qUnary
  have dUnary : UnaryHistory d := NatMul_left_unary mul
  have nUnary : UnaryHistory n := NatMul_result_unary dUnary mul
  have qProduct := NatMul_total dUnary qUnary
  cases qProduct with
  | intro e eData =>
      exact Exists.intro (append n e)
        (And.intro (unary_cont_closed nUnary eData.left (cont_intro rfl))
          (NatMul_append_cont mul eData.right (cont_intro rfl)))

end BEDC.Derived.PrimeUp
