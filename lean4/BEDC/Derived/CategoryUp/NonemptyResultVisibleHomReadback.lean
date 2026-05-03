import BEDC.Derived.CategoryUp.NonemptyCases

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_comp_nonempty_result_visible_hom_readback {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      (hsame fg BHist.Empty -> False) ->
        ∃ k r : BHist, fg = BHist.e1 k ∧ c = BHist.e1 r ∧
          CategoryHomCarrier a (BHist.e1 r) (BHist.e1 k) := by
  intro left right comp resultNonempty
  have visible :=
    CategoryHomCarrier_comp_result_nonempty_target_visible left right comp resultNonempty
  cases visible with
  | intro k visible =>
      cases visible with
      | intro r data =>
          cases data with
          | intro fgEq data =>
              cases data with
              | intro targetEq data =>
                  exact Exists.intro k
                    (Exists.intro r
                      (And.intro fgEq
                        (And.intro targetEq
                          (And.intro left.left
                            (And.intro (unary_e1_closed data.right.left)
                            (And.intro (unary_e1_closed data.left)
                              data.right.right))))))

theorem CategoryHomCarrier_comp_nonempty_result_visible_source_hom_readback
    {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      (hsame fg BHist.Empty -> False) -> (hsame a BHist.Empty -> False) ->
        Exists (fun s : BHist => Exists (fun k : BHist => Exists (fun r : BHist =>
          a = BHist.e1 s /\ fg = BHist.e1 k /\ c = BHist.e1 r /\
            CategoryHomCarrier (BHist.e1 s) (BHist.e1 r) (BHist.e1 k)))) := by
  intro left right comp resultNonempty sourceNonempty
  have readback :=
    CategoryHomCarrier_comp_nonempty_result_visible_hom_readback left right comp resultNonempty
  cases readback with
  | intro k readback =>
      cases readback with
      | intro r data =>
          cases data with
          | intro fgEq data =>
              cases data with
              | intro cEq homCarrier =>
                  cases a with
                  | Empty =>
                      exact False.elim (sourceNonempty (hsame_refl BHist.Empty))
                  | e0 sourceTail =>
                      exact False.elim (unary_no_zero_extension left.left)
                  | e1 sourceTail =>
                      exact Exists.intro sourceTail
                        (Exists.intro k
                          (Exists.intro r
                            (And.intro rfl
                              (And.intro fgEq
                                (And.intro cEq homCarrier)))))

end BEDC.Derived.CategoryUp
