import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_nonempty_branch_equivalence {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {h k : BHist} :
    TaggedOptionHistoryClassifier S Rel h k ->
      ((hsame h BHist.Empty -> False) <-> (hsame k BHist.Empty -> False)) := by
  intro classifier
  have absentEquiv :
      hsame h BHist.Empty <-> hsame k BHist.Empty :=
    TaggedOptionHistoryClassifier_absent_branch_equivalence classifier
  constructor
  · intro notH sameK
    exact notH (absentEquiv.mpr sameK)
  · intro notK sameH
    exact notK (absentEquiv.mp sameH)

end BEDC.Derived.OptionUp
