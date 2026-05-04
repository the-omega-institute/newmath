import BEDC.Derived.IntUp

namespace BEDC.Derived.IntUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem IntPairClassifier_balanced_append_context {a b p n q m : BHist} :
    UnaryHistory a -> UnaryHistory b -> IntPairClassifier (p, n) (q, m) ->
      IntPairClassifier (append a p, append n b) (append a q, append m b) := by
  intro unaryA unaryB classified
  constructor
  · exact ⟨unary_append_closed unaryA classified.left.left,
      unary_append_closed classified.left.right unaryB⟩
  · constructor
    · exact ⟨unary_append_closed unaryA classified.right.left.left,
        unary_append_closed classified.right.left.right unaryB⟩
    · have leftAssoc : hsame (append (append a p) (append m b))
          (append a (append p (append m b))) :=
        append_assoc a p (append m b)
      have leftSuffix : hsame (append a (append p (append m b)))
          (append a (append (append p m) b)) :=
        congrArg (append a) (append_assoc p m b).symm
      have middle : hsame (append a (append (append p m) b))
          (append a (append (append q n) b)) :=
        congrArg (fun t => append a (append t b)) classified.right.right
      have rightSuffix : hsame (append a (append (append q n) b))
          (append a (append q (append n b))) :=
        congrArg (append a) (append_assoc q n b)
      have rightAssoc : hsame (append a (append q (append n b)))
          (append (append a q) (append n b)) :=
        (append_assoc a q (append n b)).symm
      exact hsame_trans leftAssoc
        (hsame_trans leftSuffix (hsame_trans middle (hsame_trans rightSuffix rightAssoc)))

end BEDC.Derived.IntUp
