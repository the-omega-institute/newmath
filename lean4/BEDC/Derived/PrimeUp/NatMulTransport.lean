import BEDC.Derived.PrimeUp.NatMulCases
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

theorem NatMul_multiplier_hsame_transport {d q q' n : BHist} :
    NatMul d q n -> hsame q q' -> UnaryHistory q' ∧ NatMul d q' n := by
  intro mul sameMultiplier
  cases sameMultiplier
  exact And.intro (NatMul_right_unary mul) mul

theorem NatMul_operation_congruence {d d' q q' n n' : BHist} :
    NatMul d q n -> hsame d d' -> hsame q q' -> hsame n n' ->
      NatMul d' q' n' ∧ UnaryHistory d' ∧ UnaryHistory q' ∧
        (forall {m : BHist}, NatMul d' q' m -> hsame m n') := by
  intro mul sameD sameQ sameN
  have shiftedD := NatMul_multiplicand_hsame_transport sameD mul
  have shiftedQ := NatMul_multiplier_hsame_transport shiftedD.right sameQ
  have shiftedN := NatMul_result_hsame_transport shiftedQ.right sameN
  exact And.intro shiftedN.right
    (And.intro shiftedD.left
      (And.intro shiftedQ.left
        (by
          intro m mulM
          exact NatMul_functional shiftedD.left mulM shiftedN.right)))

theorem NatMul_append_multiplier_right_factor {d w q n e r : BHist} :
    UnaryHistory d -> UnaryHistory q -> NatMul d w n -> NatMul d (append w q) r ->
      Cont n e r -> NatMul d q e := by
  intro dUnary qUnary left combined displayed
  have rightTotal := NatMul_total dUnary qUnary
  cases rightTotal with
  | intro e' eData =>
      have composed : NatMul d (append w q) (append n e') :=
        NatMul_append_cont left eData.right (cont_intro rfl)
      have sameResult : hsame r (append n e') :=
        NatMul_functional dUnary combined composed
      have displayed' : Cont n e' r :=
        cont_result_hsame_transport (cont_intro rfl) (hsame_symm sameResult)
      have sameFactor : hsame e e' :=
        cont_left_cancel displayed displayed'
      exact (NatMul_result_hsame_transport eData.right (hsame_symm sameFactor)).right

theorem NatMul_append_multiplier_left_factor {d w q n e r : BHist} :
    UnaryHistory d -> UnaryHistory w -> NatMul d q e -> NatMul d (append w q) r ->
      Cont n e r -> NatMul d w n := by
  intro dUnary wUnary right combined displayed
  have leftTotal := NatMul_total dUnary wUnary
  cases leftTotal with
  | intro n' nData =>
      have composed : NatMul d (append w q) (append n' e) :=
        NatMul_append_cont nData.right right (cont_intro rfl)
      have sameResult : hsame r (append n' e) :=
        NatMul_functional dUnary combined composed
      have displayed' : Cont n' e r :=
        cont_result_hsame_transport (cont_intro rfl) (hsame_symm sameResult)
      have sameFactor : hsame n n' :=
        cont_right_cancel displayed displayed'
      exact (NatMul_result_hsame_transport nData.right (hsame_symm sameFactor)).right

theorem NatMul_append_multiplier_result_deterministic {d w q n e r z : BHist} :
    UnaryHistory d -> NatMul d w n -> NatMul d q e -> NatMul d (append w q) r ->
      Cont n e z -> hsame r z := by
  intro dUnary left right combined displayed
  have composed : NatMul d (append w q) z :=
    NatMul_append_cont left right displayed
  exact NatMul_functional dUnary combined composed

theorem NatDivides_divisor_hsame_transport {d d' n : BHist} :
    NatDivides d n -> hsame d d' -> UnaryHistory d' ∧ NatDivides d' n := by
  intro divides sameD
  cases divides with
  | intro q qData =>
      have transported := NatMul_multiplicand_hsame_transport sameD qData.right
      exact And.intro transported.left (Exists.intro q (And.intro qData.left transported.right))

theorem NatDivides_dividend_hsame_transport {d n n' : BHist} :
    NatDivides d n -> hsame n n' -> UnaryHistory n' ∧ NatDivides d n' := by
  intro divides sameN
  cases divides with
  | intro q qData =>
      have transported := NatMul_result_hsame_transport qData.right sameN
      have shiftedDivides : NatDivides d n' :=
        Exists.intro q (And.intro qData.left transported.right)
      exact And.intro (NatDivides_result_unary shiftedDivides) shiftedDivides

theorem NatDivides_endpoint_hsame_transport {d d' n n' : BHist} :
    NatDivides d n -> hsame d d' -> hsame n n' ->
      UnaryHistory d' ∧ UnaryHistory n' ∧ NatDivides d' n' := by
  intro divides sameD sameN
  have divisorTransported := NatDivides_divisor_hsame_transport divides sameD
  have dividendTransported := NatDivides_dividend_hsame_transport divisorTransported.right sameN
  exact And.intro divisorTransported.left
    (And.intro dividendTransported.left dividendTransported.right)

theorem NatDivides_prefix_cancellation {d x y z : BHist} :
    UnaryHistory d -> (hsame d BHist.Empty -> False) -> UnaryHistory x -> UnaryHistory y ->
      UnaryHistory z -> Cont x y z -> NatDivides d x -> NatDivides d z ->
        NatDivides d y := by
  intro dUnary dNonempty _xUnary yUnary _zUnary xyCont dividesX dividesZ
  cases dividesX with
  | intro q qData =>
      induction qData.right generalizing y z with
      | zero dUnaryZero =>
          have sameZY : hsame z y := cont_left_unit_result xyCont
          exact (NatDivides_dividend_hsame_transport dividesZ sameZY).right
      | succ previous step ih =>
          rename_i qTail n xStep
          have resultCases := NatDivides_result_cases dividesZ
          cases resultCases with
          | inl emptyCase =>
              have zEmpty : hsame z BHist.Empty := emptyCase.left
              have xStepEmpty : hsame xStep BHist.Empty :=
                (append_eq_empty_iff.mp (xyCont.symm.trans zEmpty)).left
              have dEmpty : hsame d BHist.Empty :=
                NatMul_succ_result_empty_left_empty (NatMul.succ previous step) xStepEmpty
              exact False.elim (dNonempty dEmpty)
          | inr stepCase =>
              cases stepCase with
              | intro pred predData =>
                  have displayed : Cont (append n y) d z := by
                    apply cont_intro
                    calc
                      z = append xStep y := xyCont
                      _ = append (append n d) y := congrArg (fun h => append h y) step
                      _ = append n (append d y) := append_assoc n d y
                      _ = append n (append y d) :=
                        congrArg (fun h => append n h) (unary_append_comm dUnary yUnary)
                      _ = append (append n y) d := (append_assoc n y d).symm
                  have samePred : hsame pred (append n y) :=
                    cont_right_cancel predData.right displayed
                  have shiftedDivides :
                      NatDivides d (append n y) :=
                    (NatDivides_dividend_hsame_transport predData.left samePred).right
                  exact ih (NatMul_result_unary dUnary previous) yUnary
                    (unary_append_closed (NatMul_result_unary dUnary previous) yUnary)
                    (cont_intro rfl) shiftedDivides
                    (And.intro (unary_e1_inversion qData.left) previous)

theorem NatDivides_cont_left_factor {d x y z : BHist} :
    UnaryHistory d -> (hsame d BHist.Empty -> False) -> UnaryHistory x -> UnaryHistory y ->
      UnaryHistory z -> NatDivides d y -> NatDivides d z -> Cont x y z ->
        NatDivides d x := by
  intro dUnary dNonempty xUnary yUnary zUnary dividesY dividesZ xyCont
  have yxCont : Cont y x z := by
    exact cont_intro (xyCont.trans (unary_append_comm xUnary yUnary))
  exact NatDivides_prefix_cancellation dUnary dNonempty yUnary xUnary zUnary yxCont
    dividesY dividesZ

theorem NatDivides_cont_right_factor_iff {d x y z : BHist} :
    UnaryHistory d -> (hsame d BHist.Empty -> False) -> UnaryHistory x -> UnaryHistory y ->
      UnaryHistory z -> NatDivides d x -> Cont x y z ->
        (NatDivides d z ↔ NatDivides d y) := by
  intro dUnary dNonempty xUnary yUnary zUnary dividesX xyCont
  constructor
  · intro dividesZ
    exact NatDivides_prefix_cancellation dUnary dNonempty xUnary yUnary zUnary xyCont
      dividesX dividesZ
  · intro dividesY
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
                        (NatMul_append_cont qxMul qyMul xyCont))

end BEDC.Derived.PrimeUp
