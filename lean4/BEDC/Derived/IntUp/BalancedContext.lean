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

theorem IntPairClassifier_balanced_append_context_reflection {a b p n q m : BHist} :
    UnaryHistory a -> UnaryHistory b ->
      IntPairClassifier (append a p, append n b) (append a q, append m b) ->
        IntPairClassifier (p, n) (q, m) := by
  intro _unaryA _unaryB classified
  constructor
  · exact ⟨unary_append_right_factor classified.left.left,
      unary_append_left_factor classified.left.right⟩
  · constructor
    · exact ⟨unary_append_right_factor classified.right.left.left,
        unary_append_left_factor classified.right.left.right⟩
    · have leftAssoc : hsame (append (append a p) (append m b))
          (append a (append p (append m b))) :=
        append_assoc a p (append m b)
      have leftSuffix : hsame (append a (append p (append m b)))
          (append a (append (append p m) b)) :=
        congrArg (append a) (append_assoc p m b).symm
      have leftExposed : hsame (append (append a p) (append m b))
          (append a (append (append p m) b)) :=
        hsame_trans leftAssoc leftSuffix
      have rightAssoc : hsame (append (append a q) (append n b))
          (append a (append q (append n b))) :=
        append_assoc a q (append n b)
      have rightSuffix : hsame (append a (append q (append n b)))
          (append a (append (append q n) b)) :=
        congrArg (append a) (append_assoc q n b).symm
      have rightExposed : hsame (append (append a q) (append n b))
          (append a (append (append q n) b)) :=
        hsame_trans rightAssoc rightSuffix
      have exposed : hsame (append a (append (append p m) b))
          (append a (append (append q n) b)) :=
        hsame_trans (hsame_symm leftExposed)
          (hsame_trans classified.right.right rightExposed)
      have withoutPrefix : hsame (append (append p m) b) (append (append q n) b) :=
        append_left_cancel exposed
      exact append_right_cancel withoutPrefix

theorem IntPairClassifier_signed_context_invariance {a b p n q m : BHist} :
    UnaryHistory a -> UnaryHistory b -> IntPairClassifier (p, n) (q, m) ->
      IntPairClassifier (append a p, append b n) (append a q, append b m) := by
  intro unaryA unaryB classified
  constructor
  · exact ⟨unary_append_closed unaryA classified.left.left,
      unary_append_closed unaryB classified.left.right⟩
  · constructor
    · exact ⟨unary_append_closed unaryA classified.right.left.left,
        unary_append_closed unaryB classified.right.left.right⟩
    · have commuteLeftContext :
          hsame (append b m) (append m b) :=
        unary_append_comm unaryB classified.right.left.right
      have commuteRightContext :
          hsame (append n b) (append b n) :=
        unary_append_comm classified.left.right unaryB
      have leftAssoc :
          hsame (append (append a p) (append b m))
            (append a (append p (append b m))) :=
        append_assoc a p (append b m)
      have leftCommute :
          hsame (append a (append p (append b m)))
            (append a (append p (append m b))) :=
        congrArg (fun t => append a (append p t)) commuteLeftContext
      have leftExpose :
          hsame (append a (append p (append m b)))
            (append a (append (append p m) b)) :=
        congrArg (append a) (append_assoc p m b).symm
      have middle :
          hsame (append a (append (append p m) b))
            (append a (append (append q n) b)) :=
        congrArg (fun t => append a (append t b)) classified.right.right
      have rightExpose :
          hsame (append a (append (append q n) b))
            (append a (append q (append n b))) :=
        congrArg (append a) (append_assoc q n b)
      have rightCommute :
          hsame (append a (append q (append n b)))
            (append a (append q (append b n))) :=
        congrArg (fun t => append a (append q t)) commuteRightContext
      have rightAssoc :
          hsame (append a (append q (append b n)))
            (append (append a q) (append b n)) :=
        (append_assoc a q (append b n)).symm
      exact hsame_trans leftAssoc
        (hsame_trans leftCommute
          (hsame_trans leftExpose
            (hsame_trans middle
              (hsame_trans rightExpose (hsame_trans rightCommute rightAssoc)))))

end BEDC.Derived.IntUp
