import BEDC.Derived.CategoryUp.NonemptyCases

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_comp_result_nonempty_source_target_cases {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      (hsame fg BHist.Empty -> False) ->
        (hsame a BHist.Empty ∧
          ∃ k r : BHist, fg = BHist.e1 k ∧ c = BHist.e1 r ∧ UnaryHistory k ∧
            UnaryHistory r ∧ Cont a (BHist.e1 k) (BHist.e1 r)) ∨
          (∃ s k r : BHist, a = BHist.e1 s ∧ fg = BHist.e1 k ∧ c = BHist.e1 r ∧
            UnaryHistory s ∧ UnaryHistory k ∧ UnaryHistory r ∧
              Cont (BHist.e1 s) (BHist.e1 k) (BHist.e1 r)) := by
  intro left right comp resultNonempty
  have visible :=
    CategoryHomCarrier_comp_result_nonempty_target_visible left right comp resultNonempty
  cases visible with
  | intro k visibleRest =>
      cases visibleRest with
      | intro r data =>
          cases data with
          | intro fgEq data =>
              cases data with
              | intro cEq data =>
                  cases data with
                  | intro kCarrier data =>
                      cases data with
                      | intro rCarrier rel =>
                          cases a with
                          | Empty =>
                              left
                              exact And.intro (hsame_refl BHist.Empty)
                                (Exists.intro k
                                  (Exists.intro r
                                    (And.intro fgEq
                                      (And.intro cEq
                                        (And.intro kCarrier (And.intro rCarrier rel))))))
                          | e0 s =>
                              exact False.elim (unary_no_zero_extension left.left)
                          | e1 s =>
                              right
                              exact Exists.intro s
                                (Exists.intro k
                                  (Exists.intro r
                                    (And.intro rfl
                                      (And.intro fgEq
                                        (And.intro cEq
                                          (And.intro (unary_e1_inversion left.left)
                                            (And.intro kCarrier
                                              (And.intro rCarrier rel))))))))

end BEDC.Derived.CategoryUp
