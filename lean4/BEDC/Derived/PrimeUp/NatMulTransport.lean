import BEDC.Derived.PrimeUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem NatMul_nonempty_quotient_product_extension {d q n : BHist} :
    UnaryHistory d -> UnaryHistory q -> NatMul d q n -> (hsame q BHist.Empty -> False) ->
      ∃ t : BHist, UnaryHistory t ∧ Cont d t n := by
  intro hd hq mul qNonempty
  induction mul with
  | zero _hd =>
      exact False.elim (qNonempty (hsame_refl BHist.Empty))
  | succ previous step ih =>
      have tailUnary : UnaryHistory _ := unary_e1_inversion hq
      cases previous with
      | zero _hd =>
          have sameResult : hsame _ d := cont_left_unit_result step
          exact
            Exists.intro BHist.Empty
              (And.intro unary_empty
                (cont_result_hsame_transport (cont_right_unit d) (hsame_symm sameResult)))
      | succ previousTail previousStep =>
          have prior := ih tailUnary (fun empty => not_hsame_e1_empty empty)
          cases prior with
          | intro t tData =>
              have suffixUnary : UnaryHistory (append t d) :=
                unary_cont_closed tData.left hd (cont_intro rfl)
              exact
                Exists.intro (append t d)
                  (And.intro suffixUnary
                    (cont_intro
                      (step.trans
                        ((congrArg (fun x => append x d) tData.right).trans
                          (append_assoc d t d)))))

theorem NatMul_multiplicand_hsame_transport {d d' q n : BHist} :
    hsame d d' -> NatMul d q n -> UnaryHistory d' ∧ NatMul d' q n := by
  intro sameD mul
  induction mul with
  | zero hd =>
      have shiftedD : UnaryHistory d' := unary_transport hd sameD
      exact And.intro shiftedD (NatMul.zero shiftedD)
  | succ _previous step ih =>
      have shiftedStep : Cont _ d' _ :=
        cont_hsame_transport (hsame_refl _) sameD (hsame_refl _) step
      exact And.intro ih.left (NatMul.succ ih.right shiftedStep)

theorem NatMul_result_hsame_transport {d q n n' : BHist} :
    NatMul d q n -> hsame n n' -> UnaryHistory d ∧ NatMul d q n' := by
  intro mul sameResult
  induction mul with
  | zero hd =>
      cases sameResult
      exact And.intro hd (NatMul.zero hd)
  | succ previous step ih =>
      exact And.intro (NatMul_left_unary previous)
        (NatMul.succ previous (cont_result_hsame_transport step sameResult))

theorem NatDivides_divisor_hsame_transport {d d' n : BHist} :
    NatDivides d n -> hsame d d' -> UnaryHistory d' ∧ NatDivides d' n := by
  intro divides sameD
  cases divides with
  | intro q qData =>
      have transported := NatMul_multiplicand_hsame_transport sameD qData.right
      exact And.intro transported.left (Exists.intro q (And.intro qData.left transported.right))

end BEDC.Derived.PrimeUp
