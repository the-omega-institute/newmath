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

theorem CentralizerCosetClassifier_representative_continuation_classifier_iff
    {mul : BHist -> BHist -> BHist} {a repr p q r h : BHist}
    (emptyCentral : SubgroupCentralizerCarrier mul a BHist.Empty)
    (reprCentral : SubgroupCentralizerCarrier mul a repr) (reprEmpty : hsame repr BHist.Empty) :
    Cont p q r ->
      (CentralizerCosetClassifier mul a repr r h ↔
        CentralizerCosetCarrier mul a repr p ∧
          CentralizerCosetCarrier mul a repr q ∧ CentralizerCosetCarrier mul a repr h) := by
  intro continuation
  have emptyIff :=
    CentralizerCosetClassifier_empty_continuation_classifier_iff
      (mul := mul) (a := a) (p := p) (q := q) (r := r) (h := h) emptyCentral
      continuation
  have transport :=
    CentralizerCosetClassifier_empty_representative_transport_iff
      (mul := mul) (a := a) (repr := repr) (h := r) (k := h) emptyCentral reprCentral
      reprEmpty
  constructor
  · intro classified
    have emptyCarriers := Iff.mp emptyIff (Iff.mp transport classified)
    exact And.intro
      (And.intro reprCentral (hsame_trans emptyCarriers.left.right (hsame_symm reprEmpty)))
      (And.intro
        (And.intro reprCentral
          (hsame_trans emptyCarriers.right.left.right (hsame_symm reprEmpty)))
        (And.intro reprCentral
          (hsame_trans emptyCarriers.right.right.right (hsame_symm reprEmpty))))
  · intro carriers
    have emptyCarriers :
        CentralizerCosetCarrier mul a BHist.Empty p ∧
          CentralizerCosetCarrier mul a BHist.Empty q ∧
            CentralizerCosetCarrier mul a BHist.Empty h :=
      And.intro (And.intro emptyCentral (hsame_trans carriers.left.right reprEmpty))
        (And.intro (And.intro emptyCentral (hsame_trans carriers.right.left.right reprEmpty))
          (And.intro emptyCentral (hsame_trans carriers.right.right.right reprEmpty)))
    exact Iff.mpr transport (Iff.mpr emptyIff emptyCarriers)

theorem QuotientGroupSingletonClassifier_continuation_classifier_iff {p q r h : BHist} :
    Cont p q r ->
      (QuotientGroupSingletonClassifier r h ↔
        QuotientGroupSingletonCarrier p ∧ QuotientGroupSingletonCarrier q ∧
          QuotientGroupSingletonCarrier h) := by
  intro continuation
  constructor
  · intro classified
    have splitEmpty := append_eq_empty_iff.mp (continuation.symm.trans classified.left)
    exact And.intro splitEmpty.left (And.intro splitEmpty.right classified.right.left)
  · intro carriers
    have resultEmpty : hsame r BHist.Empty :=
      continuation.trans (append_eq_empty_iff.mpr (And.intro carriers.left carriers.right.left))
    exact And.intro resultEmpty
      (And.intro carriers.right.right
        (hsame_trans resultEmpty (hsame_symm carriers.right.right)))

end BEDC.Derived.QuotientGroupUp
