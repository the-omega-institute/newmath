import BEDC.Derived.ProdUp

namespace BEDC.Derived.ProdUp

open BEDC.FKernel.Hist

theorem ProdComponentHistoryClassifier_source_refinement
    {Left Right Left' Right' : BHist → Prop}
    {LeftEq RightEq LeftEq' RightEq' : BHist → BHist → Prop}
    (left_carrier : ∀ {u : BHist}, Left u → Left' u)
    (right_carrier : ∀ {u : BHist}, Right u → Right' u)
    (left_rel : ∀ {a b : BHist}, LeftEq a b → LeftEq' a b)
    (right_rel : ∀ {a b : BHist}, RightEq a b → RightEq' a b) {h k : BHist} :
    ProdComponentHistoryClassifier Left Right LeftEq RightEq h k →
      ProdComponentHistoryClassifier Left' Right' LeftEq' RightEq' h k := by
  intro classifier
  cases classifier with
  | intro lh restLH =>
      cases restLH with
      | intro rh restRH =>
          cases restRH with
          | intro lk restLK =>
              cases restLK with
              | intro rk data =>
                  cases data with
                  | intro leftH rest =>
                      cases rest with
                      | intro rightH rest =>
                          cases rest with
                          | intro contH rest =>
                              cases rest with
                              | intro leftK rest =>
                                  cases rest with
                                  | intro rightK rest =>
                                      cases rest with
                                      | intro contK componentRel =>
                                          cases componentRel with
                                          | intro sameLeft sameRight =>
                                              exact Exists.intro lh
                                                (Exists.intro rh
                                                  (Exists.intro lk
                                                    (Exists.intro rk
                                                      (And.intro (left_carrier leftH)
                                                        (And.intro (right_carrier rightH)
                                                          (And.intro contH
                                                            (And.intro (left_carrier leftK)
                                                              (And.intro
                                                                (right_carrier rightK)
                                                                (And.intro contK
                                                                  (And.intro
                                                                    (left_rel sameLeft)
                                                                    (right_rel
                                                                      sameRight)))))))))))

end BEDC.Derived.ProdUp
