import BEDC.Derived.ProdUp

namespace BEDC.Derived.ProdUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ProdComponentHistoryClassifier_empty_source_exclusion {Left Right : BHist -> Prop}
    {LeftEq RightEq : BHist -> BHist -> Prop} :
    (forall {h k : BHist},
        ((forall l : BHist, Left l -> False) ∨ (forall r : BHist, Right r -> False)) ->
          ProdComponentHistoryClassifier Left Right LeftEq RightEq h k -> False) ∧
      (forall {h k : BHist},
        ProdComponentHistoryClassifier Left Right LeftEq RightEq h k ->
          exists lh : BHist, exists rh : BHist, exists lk : BHist, exists rk : BHist,
            Cont lh rh h ∧ Cont lk rk k) := by
  constructor
  · intro h k emptySource classifier
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
                        | intro rightH _rest =>
                            cases emptySource with
                            | inl noLeft =>
                                exact noLeft lh leftH
                            | inr noRight =>
                                exact noRight rh rightH
  · intro h k classifier
    cases classifier with
    | intro lh restLH =>
        cases restLH with
        | intro rh restRH =>
            cases restRH with
            | intro lk restLK =>
                cases restLK with
                | intro rk data =>
                    cases data with
                    | intro _leftH rest =>
                        cases rest with
                        | intro _rightH rest =>
                            cases rest with
                            | intro contH rest =>
                                cases rest with
                                | intro _leftK rest =>
                                    cases rest with
                                    | intro _rightK rest =>
                                        cases rest with
                                        | intro contK _componentSame =>
                                            exact Exists.intro lh
                                              (Exists.intro rh
                                                (Exists.intro lk
                                                  (Exists.intro rk
                                                    (And.intro contH contK))))

end BEDC.Derived.ProdUp
