import BEDC.Derived.CategoryUp.TargetCases

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_e1_source_e1_target_nonempty_morphism_tail_carrier_alignment
    {a r m n : BHist} :
    CategoryHomCarrier (BHist.e1 a) (BHist.e1 r) m ->
      CategoryHomCarrier (BHist.e1 a) (BHist.e1 r) n ->
        (hsame m BHist.Empty -> False) ->
          exists k : BHist, exists l : BHist, m = BHist.e1 k /\ n = BHist.e1 l /\
            CategoryHomCarrier (BHist.e1 a) r k /\
              CategoryHomCarrier (BHist.e1 a) r l /\ hsame k l := by
  intro left right nonempty
  have alignment :=
    CategoryHomCarrier_e1_source_e1_target_nonempty_morphism_tail_cont_alignment
      left right nonempty
  cases alignment with
  | intro k alignment =>
      cases alignment with
      | intro l data =>
          cases data with
          | intro mEq data =>
              cases data with
              | intro nEq data =>
                  cases data with
                  | intro kCarrier data =>
                      cases data with
                      | intro lCarrier data =>
                          cases data with
                          | intro kCont data =>
                              cases data with
                              | intro lCont sameKL =>
                                  have sourceCarrier : UnaryHistory (BHist.e1 a) := left.left
                                  have kTargetCarrier : UnaryHistory r :=
                                    unary_cont_closed sourceCarrier kCarrier kCont
                                  have lTargetCarrier : UnaryHistory r :=
                                    unary_cont_closed sourceCarrier lCarrier lCont
                                  have kHom : CategoryHomCarrier (BHist.e1 a) r k :=
                                    And.intro sourceCarrier
                                      (And.intro kTargetCarrier (And.intro kCarrier kCont))
                                  have lHom : CategoryHomCarrier (BHist.e1 a) r l :=
                                    And.intro sourceCarrier
                                      (And.intro lTargetCarrier (And.intro lCarrier lCont))
                                  exact Exists.intro k
                                    (Exists.intro l
                                      (And.intro mEq
                                        (And.intro nEq
                                          (And.intro kHom (And.intro lHom sameKL)))))

end BEDC.Derived.CategoryUp
