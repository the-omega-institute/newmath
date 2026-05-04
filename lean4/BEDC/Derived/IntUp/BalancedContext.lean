import BEDC.Derived.IntUp

namespace BEDC.Derived.IntUp

theorem IntPairClassifier_balanced_append_context
    {a b p n q m : BEDC.FKernel.Hist.BHist} :
    BEDC.FKernel.Unary.UnaryHistory a ->
      BEDC.FKernel.Unary.UnaryHistory b ->
        IntPairClassifier (p, n) (q, m) ->
          IntPairClassifier
            (BEDC.FKernel.Cont.append a p, BEDC.FKernel.Cont.append n b)
            (BEDC.FKernel.Cont.append a q, BEDC.FKernel.Cont.append m b) := by
  intro unaryA unaryB classified
  constructor
  · exact ⟨BEDC.FKernel.Unary.unary_append_closed unaryA classified.left.left,
      BEDC.FKernel.Unary.unary_append_closed classified.left.right unaryB⟩
  · constructor
    · exact ⟨BEDC.FKernel.Unary.unary_append_closed unaryA classified.right.left.left,
        BEDC.FKernel.Unary.unary_append_closed classified.right.left.right unaryB⟩
    · have leftAssoc : BEDC.FKernel.Hist.hsame
          (BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append a p)
            (BEDC.FKernel.Cont.append m b))
          (BEDC.FKernel.Cont.append a
            (BEDC.FKernel.Cont.append p (BEDC.FKernel.Cont.append m b))) :=
        BEDC.FKernel.Cont.append_assoc a p (BEDC.FKernel.Cont.append m b)
      have leftSuffix : BEDC.FKernel.Hist.hsame
          (BEDC.FKernel.Cont.append a
            (BEDC.FKernel.Cont.append p (BEDC.FKernel.Cont.append m b)))
          (BEDC.FKernel.Cont.append a
            (BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append p m) b)) :=
        congrArg (BEDC.FKernel.Cont.append a)
          (BEDC.FKernel.Cont.append_assoc p m b).symm
      have middle : BEDC.FKernel.Hist.hsame
          (BEDC.FKernel.Cont.append a
            (BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append p m) b))
          (BEDC.FKernel.Cont.append a
            (BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append q n) b)) :=
        congrArg (fun x => BEDC.FKernel.Cont.append a (BEDC.FKernel.Cont.append x b))
          classified.right.right
      have rightSuffix : BEDC.FKernel.Hist.hsame
          (BEDC.FKernel.Cont.append a
            (BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append q n) b))
          (BEDC.FKernel.Cont.append a
            (BEDC.FKernel.Cont.append q (BEDC.FKernel.Cont.append n b))) :=
        congrArg (BEDC.FKernel.Cont.append a) (BEDC.FKernel.Cont.append_assoc q n b)
      have rightAssoc : BEDC.FKernel.Hist.hsame
          (BEDC.FKernel.Cont.append a
            (BEDC.FKernel.Cont.append q (BEDC.FKernel.Cont.append n b)))
          (BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append a q)
            (BEDC.FKernel.Cont.append n b)) :=
        (BEDC.FKernel.Cont.append_assoc a q (BEDC.FKernel.Cont.append n b)).symm
      exact BEDC.FKernel.Hist.hsame_trans leftAssoc
        (BEDC.FKernel.Hist.hsame_trans leftSuffix
          (BEDC.FKernel.Hist.hsame_trans middle
            (BEDC.FKernel.Hist.hsame_trans rightSuffix rightAssoc)))

end BEDC.Derived.IntUp
