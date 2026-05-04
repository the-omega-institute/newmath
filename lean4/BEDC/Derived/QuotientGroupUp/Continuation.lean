import BEDC.Derived.QuotientGroupUp

namespace BEDC.Derived.QuotientGroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.SubgroupUp

theorem CentralizerCosetClassifier_empty_continuation_classifier_iff
    {mul : BHist -> BHist -> BHist} {a p q r h : BHist}
    (emptyCentral : SubgroupCentralizerCarrier mul a BHist.Empty) :
    Cont p q r ->
      (CentralizerCosetClassifier mul a BHist.Empty r h ↔
        CentralizerCosetCarrier mul a BHist.Empty p ∧
          CentralizerCosetCarrier mul a BHist.Empty q ∧
            CentralizerCosetCarrier mul a BHist.Empty h) := by
  intro continuation
  constructor
  · intro classified
    have resultEmpty : hsame r BHist.Empty := classified.left.right
    have splitEmpty := append_eq_empty_iff.mp (continuation.symm.trans resultEmpty)
    exact And.intro (And.intro emptyCentral splitEmpty.left)
      (And.intro (And.intro emptyCentral splitEmpty.right) classified.right.left)
  · intro carriers
    have resultEmpty : hsame r BHist.Empty :=
      continuation.trans (append_eq_empty_iff.mpr
        (And.intro carriers.left.right carriers.right.left.right))
    exact And.intro (And.intro emptyCentral resultEmpty)
      (And.intro carriers.right.right
        (hsame_trans resultEmpty (hsame_symm carriers.right.right.right)))

end BEDC.Derived.QuotientGroupUp
