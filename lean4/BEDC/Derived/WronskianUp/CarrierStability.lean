import BEDC.Derived.WronskianUp.TasteGate

namespace BEDC.Derived.WronskianUp

open BEDC.FKernel.Hist

theorem WronskianCarrier_classifier_stability
    {F D J Omega S R E H C P N read read' : BHist} :
    WronskianObligationRowSpec F D J Omega S R E H C P N read →
      hsame read read' →
        WronskianObligationRowSpec F D J Omega S R E H C P N read' := by
  -- BEDC touchpoint anchor: BHist hsame WronskianObligationRowSpec
  intro source sameRead
  have sameRead' : hsame read' read := hsame_symm sameRead
  cases source with
  | inl sameF =>
      exact Or.inl (hsame_trans sameRead' sameF)
  | inr rest =>
      cases rest with
      | inl sameD =>
          exact Or.inr (Or.inl (hsame_trans sameRead' sameD))
      | inr rest =>
          cases rest with
          | inl sameJ =>
              exact Or.inr (Or.inr (Or.inl (hsame_trans sameRead' sameJ)))
          | inr rest =>
              cases rest with
              | inl sameOmega =>
                  exact
                    Or.inr (Or.inr (Or.inr (Or.inl (hsame_trans sameRead' sameOmega))))
              | inr rest =>
                  cases rest with
                  | inl sameS =>
                      exact
                        Or.inr
                          (Or.inr (Or.inr (Or.inr (Or.inl (hsame_trans sameRead' sameS)))))
                  | inr rest =>
                      cases rest with
                      | inl sameR =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr (Or.inl (hsame_trans sameRead' sameR))))))
                      | inr rest =>
                          cases rest with
                          | inl sameE =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr (Or.inl (hsame_trans sameRead' sameE)))))))
                          | inr rest =>
                              cases rest with
                              | inl sameH =>
                                  exact
                                    Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans sameRead' sameH))))))))
                              | inr rest =>
                                  cases rest with
                                  | inl sameC =>
                                      exact
                                        Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inl
                                                          (hsame_trans sameRead'
                                                            sameC)))))))))
                                  | inr rest =>
                                      cases rest with
                                      | inl sameP =>
                                          exact
                                            Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inl
                                                                (hsame_trans sameRead'
                                                                  sameP))))))))))
                                      | inr sameN =>
                                          exact
                                            Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inr
                                                                (hsame_trans sameRead'
                                                                  sameN))))))))))

end BEDC.Derived.WronskianUp
