import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.PolynomialUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem PolynomialSingletonRawAdd_commutative_classified {xs ys : List BHist} :
    BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier xs xs ->
      BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier ys ys ->
        BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier
            (PolynomialSingletonRawAdd xs ys) (PolynomialSingletonRawAdd ys xs) ∧
          Cont (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs ys)) BHist.Empty
            (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs ys)) := by
  intro classifiedXS
  induction xs generalizing ys with
  | nil =>
      intro classifiedYS
      induction ys with
      | nil =>
          constructor
          · unfold PolynomialSingletonRawAdd
            exact classifiedXS
          · exact cont_right_unit (PolynomialSingletonAddFold (PolynomialSingletonRawAdd [] []))
      | cons y ys ih =>
          cases classifiedYS with
          | intro headClassified tailClassified =>
              have headSwap :
                  PolynomialSingletonClassifier (append BHist.Empty y) (append y BHist.Empty) :=
                (PolynomialSingletonClassifier_continuation_comm_closed
                  (hsame_refl BHist.Empty) headClassified.left (cont_intro rfl)
                  (cont_intro rfl)).right.right
              have tailSwap := ih tailClassified
              constructor
              · unfold PolynomialSingletonRawAdd
                exact And.intro headSwap tailSwap.left
              · exact cont_right_unit
                  (PolynomialSingletonAddFold (PolynomialSingletonRawAdd [] (y :: ys)))
  | cons x xs ih =>
      intro classifiedYS
      cases classifiedXS with
      | intro headXClassified tailXClassified =>
          cases ys with
          | nil =>
              have nilClassified :
                  BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier [] [] := by
                constructor
              have tailSwap := ih tailXClassified nilClassified
              have headSwap :
                  PolynomialSingletonClassifier (append x BHist.Empty) (append BHist.Empty x) :=
                (PolynomialSingletonClassifier_continuation_comm_closed headXClassified.left
                  (hsame_refl BHist.Empty) (cont_intro rfl) (cont_intro rfl)).right.right
              constructor
              · unfold PolynomialSingletonRawAdd
                exact And.intro headSwap tailSwap.left
              · exact cont_right_unit
                  (PolynomialSingletonAddFold (PolynomialSingletonRawAdd (x :: xs) []))
          | cons y ys =>
              cases classifiedYS with
              | intro headYClassified tailYClassified =>
                  have headSwap :
                      PolynomialSingletonClassifier (append x y) (append y x) :=
                    (PolynomialSingletonClassifier_continuation_comm_closed
                      headXClassified.left headYClassified.left (cont_intro rfl)
                      (cont_intro rfl)).right.right
                  have tailSwap := ih tailXClassified tailYClassified
                  constructor
                  · unfold PolynomialSingletonRawAdd
                    exact And.intro headSwap tailSwap.left
                  · exact cont_right_unit
                      (PolynomialSingletonAddFold
                        (PolynomialSingletonRawAdd (x :: xs) (y :: ys)))

end BEDC.Derived.PolynomialUp
