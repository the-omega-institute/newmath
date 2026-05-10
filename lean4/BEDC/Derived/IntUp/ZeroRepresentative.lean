import BEDC.Derived.IntUp

namespace BEDC.Derived.IntUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem IntPairClassifier_zero_representative_criterion {p n : BHist} :
    UnaryHistory p -> UnaryHistory n ->
      (IntPairClassifier (p, n) (BHist.Empty, BHist.Empty) <-> hsame p n) ∧
        (IntPairClassifier (BHist.Empty, BHist.Empty) (p, n) <-> hsame p n) := by
  intro unaryP unaryN
  constructor
  · constructor
    · intro classified
      exact hsame_trans (hsame_symm (append_empty_right p))
        (hsame_trans classified.right.right (append_empty_left n))
    · intro samePN
      exact And.intro (And.intro unaryP unaryN)
        (And.intro (And.intro unary_empty unary_empty)
          (hsame_trans (append_empty_right p)
            (hsame_trans samePN (hsame_symm (append_empty_left n)))))
  · constructor
    · intro classified
      exact hsame_trans (hsame_symm (append_empty_right p))
        (hsame_trans (hsame_symm classified.right.right) (append_empty_left n))
    · intro samePN
      exact And.intro (And.intro unary_empty unary_empty)
        (And.intro (And.intro unaryP unaryN)
          (hsame_trans (append_empty_left n)
            (hsame_trans (hsame_symm samePN) (hsame_symm (append_empty_right p)))))

end BEDC.Derived.IntUp
