import BEDC.Derived.IntUp

namespace BEDC.Derived.IntUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem IntPairClassifier_canonical_same_sign_readback_iff {m n : BHist} :
    (IntPairClassifier (m, BHist.Empty) (n, BHist.Empty) ↔
      UnaryHistory m ∧ UnaryHistory n ∧ hsame m n) ∧
      (IntPairClassifier (BHist.Empty, m) (BHist.Empty, n) ↔
        UnaryHistory m ∧ UnaryHistory n ∧ hsame m n) := by
  constructor
  · constructor
    · intro classified
      exact
        And.intro classified.left.left
          (And.intro classified.right.left.left
            (hsame_trans (hsame_symm (append_empty_right m))
              (hsame_trans classified.right.right (append_empty_right n))))
    · intro data
      exact
        And.intro (And.intro data.left unary_empty)
          (And.intro (And.intro data.right.left unary_empty)
            (hsame_trans (append_empty_right m)
              (hsame_trans data.right.right (hsame_symm (append_empty_right n)))))
  · constructor
    · intro classified
      exact
        And.intro classified.left.right
          (And.intro classified.right.left.right
            (hsame_trans (hsame_symm (append_empty_left m))
              (hsame_trans (hsame_symm classified.right.right) (append_empty_left n))))
    · intro data
      exact
        And.intro (And.intro unary_empty data.left)
          (And.intro (And.intro unary_empty data.right.left)
            (hsame_trans (append_empty_left n)
              (hsame_trans (hsame_symm data.right.right)
                (hsame_symm (append_empty_left m)))))

end BEDC.Derived.IntUp
