import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

private theorem NatUnaryStrictPrefix_successor_gap_absurd {r t : BHist} :
    NatUnaryStrictPrefix r t -> NatUnaryStrictPrefix t (BHist.e1 r) -> False := by
  intro left right
  cases left with
  | intro leftTail leftData =>
      cases leftData with
      | intro leftUnary leftRest =>
          cases leftRest with
          | intro leftNonempty leftCont =>
              cases right with
              | intro rightTail rightData =>
                  cases rightData with
                  | intro rightUnary rightRest =>
                      cases rightRest with
                      | intro rightNonempty rightCont =>
                          have composite : Cont r (append leftTail rightTail) (BHist.e1 r) := by
                            exact cont_intro
                              (rightCont.trans
                                ((congrArg (fun y => append y rightTail) leftCont).trans
                                  (append_assoc r leftTail rightTail)))
                          have direct : Cont r (BHist.e1 BHist.Empty) (BHist.e1 r) :=
                            cont_intro rfl
                          have tailSame :
                              hsame (append leftTail rightTail) (BHist.e1 BHist.Empty) :=
                            cont_left_cancel composite direct
                          cases leftTail with
                          | Empty =>
                              exact leftNonempty rfl
                          | e0 leftTail =>
                              cases leftUnary
                          | e1 leftTail =>
                              cases rightTail with
                              | Empty =>
                                  exact rightNonempty rfl
                              | e0 rightTail =>
                                  cases rightUnary
                              | e1 rightTail =>
                                  have innerEmpty :
                                      hsame (append (BHist.e1 leftTail) rightTail) BHist.Empty :=
                                    BHist.e1.inj tailSame
                                  exact not_hsame_e1_empty
                                    (append_eq_empty_iff.mp innerEmpty).left

theorem NatMul_division_with_remainder {t x : BHist} :
    UnaryHistory t -> UnaryHistory x -> (hsame t BHist.Empty -> False) ->
      exists q r w : BHist,
        UnaryHistory q ∧ UnaryHistory r ∧ UnaryHistory w ∧ NatMul t q w ∧ Cont w r x ∧
          (hsame r BHist.Empty ∨ NatUnaryStrictPrefix r t) := by
  intro tUnary xUnary tNonempty
  induction x with
  | Empty =>
      exact ⟨BHist.Empty, BHist.Empty, BHist.Empty, unary_empty, unary_empty, unary_empty,
        NatMul.zero tUnary, cont_right_unit BHist.Empty, Or.inl rfl⟩
  | e0 x =>
      cases xUnary
  | e1 x ih =>
      have xTailUnary : UnaryHistory x := unary_e1_inversion xUnary
      cases ih xTailUnary with
      | intro q qRest =>
          cases qRest with
          | intro r rRest =>
              cases rRest with
              | intro w data =>
                  cases data with
                  | intro qUnary data =>
                      cases data with
                      | intro rUnary data =>
                          cases data with
                          | intro wUnary data =>
                              cases data with
                              | intro mul data =>
                                  cases data with
                                  | intro displayed remainderBound =>
                                      have nextRUnary : UnaryHistory (BHist.e1 r) :=
                                        unary_e1_closed rUnary
                                      have nextDisplayed :
                                          Cont w (BHist.e1 r) (BHist.e1 x) := by
                                        cases displayed
                                        rfl
                                      have total := NatUnaryPrefix_total nextRUnary tUnary
                                      cases total with
                                      | inl nextPrefix =>
                                          cases nextPrefix with
                                          | intro tail tailData =>
                                              cases NatUnaryPrefix_cont_tail_cases
                                                  tailData.left tailData.right with
                                              | inl nextSame =>
                                                  have step :
                                                      Cont w t (BHist.e1 x) :=
                                                    cont_hsame_transport (hsame_refl w)
                                                      nextSame (hsame_refl (BHist.e1 x))
                                                      nextDisplayed
                                                  exact
                                                    ⟨BHist.e1 q, BHist.Empty, BHist.e1 x,
                                                      unary_e1_closed qUnary, unary_empty,
                                                      xUnary, NatMul.succ mul step,
                                                      cont_right_unit (BHist.e1 x), Or.inl rfl⟩
                                              | inr nextStrict =>
                                                  exact
                                                    ⟨q, BHist.e1 r, w, qUnary, nextRUnary,
                                                      wUnary, mul, nextDisplayed,
                                                      Or.inr nextStrict⟩
                                      | inr tPrefix =>
                                          cases tPrefix with
                                          | intro tail tailData =>
                                              cases NatUnaryPrefix_cont_tail_cases
                                                  tailData.left tailData.right with
                                              | inl sameTNext =>
                                                  have step :
                                                      Cont w t (BHist.e1 x) :=
                                                    cont_hsame_transport (hsame_refl w)
                                                      (hsame_symm sameTNext)
                                                      (hsame_refl (BHist.e1 x)) nextDisplayed
                                                  exact
                                                    ⟨BHist.e1 q, BHist.Empty, BHist.e1 x,
                                                      unary_e1_closed qUnary, unary_empty,
                                                      xUnary, NatMul.succ mul step,
                                                      cont_right_unit (BHist.e1 x), Or.inl rfl⟩
                                              | inr overshoot =>
                                                  have baseStrict : NatUnaryStrictPrefix r t := by
                                                    cases remainderBound with
                                                    | inl rEmpty =>
                                                        cases rEmpty
                                                        exact ⟨t, tUnary, tNonempty,
                                                          cont_left_unit t⟩
                                                    | inr strict =>
                                                        exact strict
                                                  exact False.elim
                                                    (NatUnaryStrictPrefix_successor_gap_absurd
                                                      baseStrict overshoot)

end BEDC.Derived.PrimeUp
