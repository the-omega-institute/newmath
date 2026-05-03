import BEDC.Derived.CategoryUp.TargetCases

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_comp_nonempty_e1_morphism_tail_result_descent {a b c f g k : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g (BHist.e1 k) ->
      (hsame f BHist.Empty -> False) -> (hsame g BHist.Empty -> False) ->
        ∃ l m r s : BHist, f = BHist.e1 l ∧ g = BHist.e1 m ∧ b = BHist.e1 r ∧
          c = BHist.e1 s ∧ CategoryHomCarrier a r l ∧
            CategoryHomCarrier (BHist.e1 r) s m ∧ Cont (BHist.e1 l) m k ∧
              CategoryHomCarrier a s k := by
  intro left right comp nonemptyF nonemptyG
  have factors :=
    CategoryHomCarrier_comp_nonempty_e1_morphism_factors left right comp nonemptyF nonemptyG
  cases factors with
  | intro l factors =>
      cases factors with
      | intro m factors =>
          cases factors with
          | intro r factors =>
              cases factors with
              | intro s data =>
                  cases data with
                  | intro fEq data =>
                      cases data with
                      | intro gEq data =>
                          cases data with
                          | intro bEq data =>
                              cases data with
                              | intro cEq data =>
                                  cases data with
                                  | intro leftTail data =>
                                      cases data with
                                      | intro rightTail visibleComp =>
                                          have tailCont : Cont (BHist.e1 l) m k :=
                                            BHist.e1.inj visibleComp
                                          have resultCarrier : CategoryHomCarrier a s k := by
                                            have sourceCarrier : UnaryHistory a := leftTail.left
                                            have targetCarrier : UnaryHistory s :=
                                              rightTail.right.left
                                            have lCarrier : UnaryHistory l :=
                                              leftTail.right.right.left
                                            have mCarrier : UnaryHistory m :=
                                              rightTail.right.right.left
                                            have morphCarrier : UnaryHistory k :=
                                              unary_cont_closed (unary_e1_closed lCarrier)
                                                mCarrier tailCont
                                            have resultCont : Cont a k s := by
                                              cases leftTail.right.right.right
                                              cases tailCont
                                              cases rightTail.right.right.right
                                              exact append_assoc a (BHist.e1 l) m
                                            exact And.intro sourceCarrier
                                              (And.intro targetCarrier
                                                (And.intro morphCarrier resultCont))
                                          exact Exists.intro l
                                            (Exists.intro m
                                              (Exists.intro r
                                                (Exists.intro s
                                                  (And.intro fEq
                                                    (And.intro gEq
                                                      (And.intro bEq
                                                        (And.intro cEq
                                                          (And.intro leftTail
                                                            (And.intro rightTail
                                                              (And.intro tailCont
                                                                resultCarrier))))))))))

end BEDC.Derived.CategoryUp
