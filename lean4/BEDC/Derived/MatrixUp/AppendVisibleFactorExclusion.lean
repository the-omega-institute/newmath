import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem MatrixSingletonClassifier_append_visible_factor_exclusion {h p q : BHist} :
    (MatrixSingletonClassifier (append (BHist.e0 p) q) h -> False) ∧
      (MatrixSingletonClassifier h (append (BHist.e0 p) q) -> False) ∧
        (MatrixSingletonClassifier (append (BHist.e1 p) q) h -> False) ∧
          (MatrixSingletonClassifier h (append (BHist.e1 p) q) -> False) ∧
            (MatrixSingletonClassifier (append p (BHist.e0 q)) h -> False) ∧
              (MatrixSingletonClassifier h (append p (BHist.e0 q)) -> False) ∧
                (MatrixSingletonClassifier (append p (BHist.e1 q)) h -> False) ∧
                  (MatrixSingletonClassifier h (append p (BHist.e1 q)) -> False) := by
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    cases emptyParts.left
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.right.left
    cases emptyParts.left
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    cases emptyParts.left
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.right.left
    cases emptyParts.left
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    cases emptyParts.right
  constructor
  · exact MatrixSingletonClassifier_append_visible_right_absurd.left
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    cases emptyParts.right
  · exact MatrixSingletonClassifier_append_visible_right_absurd.right

end BEDC.Derived.MatrixUp
