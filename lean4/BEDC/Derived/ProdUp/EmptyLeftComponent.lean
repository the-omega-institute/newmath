import BEDC.Derived.ProdUp

namespace BEDC.Derived.ProdUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ProdHistoryClassifier_empty_left_component_inversion {Left Right : BHist -> Prop}
    {k : BHist} :
    ProdHistoryClassifier Left Right BHist.Empty k ->
      exists l : BHist, exists r : BHist, exists l' : BHist, exists r' : BHist,
        Left l /\ Right r /\ hsame l BHist.Empty /\ hsame r BHist.Empty /\
          Left l' /\ Right r' /\ Cont l' r' k /\ hsame BHist.Empty k := by
  intro classifier
  have exposed :=
    (ProdHistoryClassifier_component_inversion (Left := Left) (Right := Right)
      (h := BHist.Empty) (k := k)).mp classifier
  cases exposed with
  | intro l rest =>
      cases rest with
      | intro r rest =>
          cases rest with
          | intro l' rest =>
              cases rest with
              | intro r' data =>
                  cases data with
                  | intro leftL rest =>
                      cases rest with
                      | intro rightR rest =>
                          cases rest with
                          | intro contEmpty rest =>
                              cases rest with
                              | intro leftL' rest =>
                                  cases rest with
                                  | intro rightR' rest =>
                                      cases rest with
                                      | intro contK sameEmptyK =>
                                          have emptyParts :=
                                            cont_empty_result_inversion contEmpty
                                          exact Exists.intro l
                                            (Exists.intro r
                                              (Exists.intro l'
                                                (Exists.intro r'
                                                  (And.intro leftL
                                                    (And.intro rightR
                                                      (And.intro emptyParts.left
                                                        (And.intro emptyParts.right
                                                          (And.intro leftL'
                                                            (And.intro rightR'
                                                              (And.intro contK
                                                                sameEmptyK))))))))))

end BEDC.Derived.ProdUp
