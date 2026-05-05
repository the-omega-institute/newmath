import BEDC.Derived.PrimeUp.NatMulComm

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem NatMul_nonempty_multiplicand_result_cancel {d q r n m : BHist} :
    UnaryHistory d -> (hsame d BHist.Empty -> False) ->
      NatMul d q n -> NatMul d r m -> hsame n m -> hsame q r := by
  intro hd dNonempty left
  induction left generalizing r m with
  | zero _hd =>
      intro right sameResult
      cases sameResult
      have rEmpty : hsame r BHist.Empty :=
        (NatMul_nonempty_multiplicand_empty_result_iff hd dNonempty).mp right
      exact hsame_symm rEmpty
  | succ leftPrev leftCont ih =>
      intro right sameResult
      cases right with
      | zero _hd =>
          cases sameResult
          have emptyParts := cont_empty_result_inversion leftCont
          exact False.elim (dNonempty emptyParts.right)
      | succ rightPrev rightCont =>
          have samePrev : hsame _ _ :=
            cont_common_suffix_cancellation leftCont rightCont sameResult
          exact hsame_e1_congr (ih rightPrev samePrev)

theorem NatMul_nonempty_multiplier_result_cancel {d r q n m : BHist} :
    UnaryHistory q -> (hsame q BHist.Empty -> False) ->
      NatMul d q n -> NatMul r q m -> hsame n m -> hsame d r := by
  intro qUnary qNonempty left right sameResult
  have dUnary : UnaryHistory d := NatMul_left_unary left
  have rUnary : UnaryHistory r := NatMul_left_unary right
  cases NatMul_total qUnary dUnary with
  | intro reverseLeft reverseLeftData =>
      cases NatMul_total qUnary rUnary with
      | intro reverseRight reverseRightData =>
          have sameLeft :
              hsame n reverseLeft :=
            NatMul_comm_hsame dUnary qUnary left reverseLeftData.right
          have sameRight :
              hsame m reverseRight :=
            NatMul_comm_hsame rUnary qUnary right reverseRightData.right
          have sameReverse :
              hsame reverseLeft reverseRight :=
            hsame_trans (hsame_symm sameLeft) (hsame_trans sameResult sameRight)
          exact
            NatMul_nonempty_multiplicand_result_cancel qUnary qNonempty
              reverseLeftData.right reverseRightData.right sameReverse

end BEDC.Derived.PrimeUp
