import BEDC.Derived.PrimeUp
import BEDC.Derived.PrimeUp.NatMulComm
import BEDC.Derived.PrimeUp.NatMulTransport

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

theorem NatDivides_mul_right_closed {d q n : BHist} :
    UnaryHistory d -> UnaryHistory q -> NatMul d q n -> NatDivides q n := by
  intro dUnary qUnary mul
  have qProduct := NatMul_total qUnary dUnary
  cases qProduct with
  | intro m mData =>
      have sameResult : hsame n m := NatMul_comm_hsame dUnary qUnary mul mData.right
      have dividesM : NatDivides q m := Exists.intro d (And.intro dUnary mData.right)
      exact (NatDivides_dividend_hsame_transport dividesM (hsame_symm sameResult)).right

theorem NatDivides_mul_left_closed {d x q z : BHist} :
    UnaryHistory x -> NatDivides d q -> NatMul x q z -> NatDivides d z := by
  intro xUnary divides mul
  have qUnary : UnaryHistory q := NatDivides_result_unary divides
  have qProduct := NatMul_total qUnary xUnary
  cases qProduct with
  | intro z' zData =>
      have sameProduct : hsame z z' :=
        NatMul_comm_hsame xUnary qUnary mul zData.right
      have qDividesProduct : NatDivides q z' :=
        Exists.intro x (And.intro xUnary zData.right)
      have qDividesZ : NatDivides q z :=
        (NatDivides_dividend_hsame_transport qDividesProduct (hsame_symm sameProduct)).right
      exact NatDivides_transitive divides qDividesZ

end BEDC.Derived.PrimeUp
