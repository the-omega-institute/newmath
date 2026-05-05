import BEDC.Derived.PrimeUp

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

end BEDC.Derived.PrimeUp
