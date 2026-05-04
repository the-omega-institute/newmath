import BEDC.Derived.IntUp.BalancedContext

namespace BEDC.Derived.IntUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem IntPairClassifier_one_sided_append_context_exactness {a p n q m : BHist} :
    UnaryHistory a →
      ((IntPairClassifier (append a p, n) (append a q, m) ↔
          IntPairClassifier (p, n) (q, m)) ∧
        (IntPairClassifier (p, append n a) (q, append m a) ↔
          IntPairClassifier (p, n) (q, m))) := by
  intro unaryA
  constructor
  · constructor
    · intro contextual
      constructor
      · exact ⟨unary_append_right_factor contextual.left.left, contextual.left.right⟩
      · constructor
        · exact ⟨unary_append_right_factor contextual.right.left.left,
            contextual.right.left.right⟩
        · have exposed : hsame (append a (append p m)) (append a (append q n)) :=
            hsame_trans (hsame_symm (append_assoc a p m))
              (hsame_trans contextual.right.right (append_assoc a q n))
          exact append_left_cancel exposed
    · intro classified
      exact IntPairClassifier_append_positive_context unaryA classified
  · constructor
    · intro contextual
      constructor
      · exact ⟨contextual.left.left, unary_append_left_factor contextual.left.right⟩
      · constructor
        · exact ⟨contextual.right.left.left,
            unary_append_left_factor contextual.right.left.right⟩
        · have exposed : hsame (append (append p m) a) (append (append q n) a) :=
            hsame_trans (append_assoc p m a)
              (hsame_trans contextual.right.right (hsame_symm (append_assoc q n a)))
          exact append_right_cancel exposed
    · intro classified
      constructor
      · exact ⟨classified.left.left, unary_append_closed classified.left.right unaryA⟩
      · constructor
        · exact ⟨classified.right.left.left,
            unary_append_closed classified.right.left.right unaryA⟩
        · exact hsame_trans (hsame_symm (append_assoc p m a))
            (hsame_trans (congrArg (fun t => append t a) classified.right.right)
              (append_assoc q n a))

end BEDC.Derived.IntUp
