import BEDC.Derived.QuotientGroupUp

namespace BEDC.Derived.QuotientGroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.SubgroupUp

theorem CentralizerCosetCarrier_empty_representative_transport_iff
    {mul : BHist -> BHist -> BHist} {a repr h : BHist}
    (emptyCentral : SubgroupCentralizerCarrier mul a BHist.Empty)
    (reprCentral : SubgroupCentralizerCarrier mul a repr) :
    hsame repr BHist.Empty ->
      (CentralizerCosetCarrier mul a repr h <->
        CentralizerCosetCarrier mul a BHist.Empty h) := by
  intro reprEmpty
  constructor
  · intro carrier
    exact And.intro emptyCentral (hsame_trans carrier.right reprEmpty)
  · intro carrier
    exact And.intro reprCentral (hsame_trans carrier.right (hsame_symm reprEmpty))

theorem CentralizerCosetCarrier_empty_continuation_pair_iff
    {mul : BHist -> BHist -> BHist} {a p q r : BHist}
    (emptyCentral : SubgroupCentralizerCarrier mul a BHist.Empty) :
    Cont p q r ->
      (CentralizerCosetCarrier mul a BHist.Empty r <->
        CentralizerCosetCarrier mul a BHist.Empty p ∧
          CentralizerCosetCarrier mul a BHist.Empty q) := by
  intro continuation
  constructor
  · intro resultCarrier
    have emptyContinuation : Cont p q BHist.Empty :=
      cont_result_hsame_transport continuation resultCarrier.right
    have endpoints := cont_empty_result_inversion emptyContinuation
    exact And.intro (And.intro emptyCentral endpoints.left)
      (And.intro emptyCentral endpoints.right)
  · intro endpointCarriers
    have transported : Cont p q BHist.Empty :=
      cont_result_hsame_transport continuation
        (continuation.trans
          (append_eq_empty_iff.mpr
            (And.intro endpointCarriers.left.right endpointCarriers.right.right)))
    have resultEmpty : hsame r BHist.Empty :=
      cont_deterministic continuation transported
    exact And.intro emptyCentral resultEmpty

theorem CentralizerCosetCarrier_representative_continuation_pair_iff
    {mul : BHist -> BHist -> BHist} {a repr p q r : BHist}
    (emptyCentral : SubgroupCentralizerCarrier mul a BHist.Empty)
    (reprCentral : SubgroupCentralizerCarrier mul a repr) :
    hsame repr BHist.Empty -> Cont p q r ->
      (CentralizerCosetCarrier mul a repr r <->
        CentralizerCosetCarrier mul a repr p ∧
          CentralizerCosetCarrier mul a repr q) := by
  intro reprEmpty continuation
  have emptyPair :=
    CentralizerCosetCarrier_empty_continuation_pair_iff
      (mul := mul) (a := a) (p := p) (q := q) (r := r) emptyCentral continuation
  constructor
  · intro resultCarrier
    have emptyResult : CentralizerCosetCarrier mul a BHist.Empty r :=
      And.intro emptyCentral (hsame_trans resultCarrier.right reprEmpty)
    have emptyEndpoints := Iff.mp emptyPair emptyResult
    exact And.intro
      (And.intro reprCentral (hsame_trans emptyEndpoints.left.right (hsame_symm reprEmpty)))
      (And.intro reprCentral
        (hsame_trans emptyEndpoints.right.right (hsame_symm reprEmpty)))
  · intro endpointCarriers
    have emptyEndpoints :
        CentralizerCosetCarrier mul a BHist.Empty p ∧
          CentralizerCosetCarrier mul a BHist.Empty q :=
      And.intro (And.intro emptyCentral (hsame_trans endpointCarriers.left.right reprEmpty))
        (And.intro emptyCentral (hsame_trans endpointCarriers.right.right reprEmpty))
    have emptyResult := Iff.mpr emptyPair emptyEndpoints
    exact And.intro reprCentral (hsame_trans emptyResult.right (hsame_symm reprEmpty))

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

theorem CentralizerCosetClassifier_empty_hsame_endpoint_transport
    {mul : BHist -> BHist -> BHist} {a h k h' k' : BHist} :
    CentralizerCosetClassifier mul a BHist.Empty h k -> hsame h h' -> hsame k k' ->
      CentralizerCosetClassifier mul a BHist.Empty h' k' ∧ hsame h' BHist.Empty ∧
        hsame k' BHist.Empty := by
  intro classified sameH sameK
  have endpointH : hsame h' BHist.Empty :=
    hsame_trans (hsame_symm sameH) classified.left.right
  have endpointK : hsame k' BHist.Empty :=
    hsame_trans (hsame_symm sameK) classified.right.left.right
  have carrierH : CentralizerCosetCarrier mul a BHist.Empty h' :=
    And.intro classified.left.left endpointH
  have carrierK : CentralizerCosetCarrier mul a BHist.Empty k' :=
    And.intro classified.right.left.left endpointK
  have sameHK : hsame h' k' :=
    hsame_trans endpointH (hsame_symm endpointK)
  exact And.intro (And.intro carrierH (And.intro carrierK sameHK))
    (And.intro endpointH endpointK)

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

theorem CentralizerCosetCarrier_empty_representative_context_iff
    {mul : BHist -> BHist -> BHist} {a left h right : BHist}
    (emptyCentral : SubgroupCentralizerCarrier mul a BHist.Empty) :
    CentralizerCosetCarrier mul a BHist.Empty (append left (append h right)) ↔
      CentralizerCosetCarrier mul a BHist.Empty left ∧
        CentralizerCosetCarrier mul a BHist.Empty h ∧
          CentralizerCosetCarrier mul a BHist.Empty right := by
  constructor
  · intro carrier
    have outerSplit := append_eq_empty_iff.mp carrier.right
    have innerSplit := append_eq_empty_iff.mp outerSplit.right
    exact And.intro (And.intro emptyCentral outerSplit.left)
      (And.intro (And.intro emptyCentral innerSplit.left)
        (And.intro emptyCentral innerSplit.right))
  · intro carriers
    exact And.intro emptyCentral
      (append_eq_empty_iff.mpr
        (And.intro carriers.left.right
          (append_eq_empty_iff.mpr
            (And.intro carriers.right.left.right carriers.right.right.right))))

theorem CentralizerCosetClassifier_representative_context_classifier_iff
    {mul : BHist -> BHist -> BHist} {a repr l h r k : BHist}
    (emptyCentral : SubgroupCentralizerCarrier mul a BHist.Empty)
    (reprCentral : SubgroupCentralizerCarrier mul a repr)
    (reprEmpty : hsame repr BHist.Empty) :
    CentralizerCosetClassifier mul a repr (append l (append h r)) k <->
      CentralizerCosetCarrier mul a repr l /\
        CentralizerCosetCarrier mul a repr h /\
          CentralizerCosetCarrier mul a repr r /\
            CentralizerCosetCarrier mul a repr k := by
  have classifierTransport :=
    CentralizerCosetClassifier_empty_representative_transport_iff
      (mul := mul) (a := a) (repr := repr) (h := append l (append h r)) (k := k)
      emptyCentral reprCentral reprEmpty
  have emptyContext :=
    CentralizerCosetCarrier_empty_representative_context_iff
      (mul := mul) (a := a) (left := l) (h := h) (right := r) emptyCentral
  constructor
  · intro classified
    have emptyClassified := Iff.mp classifierTransport classified
    have emptyLefts := Iff.mp emptyContext emptyClassified.left
    exact And.intro
      (And.intro reprCentral (hsame_trans emptyLefts.left.right (hsame_symm reprEmpty)))
      (And.intro
        (And.intro reprCentral (hsame_trans emptyLefts.right.left.right (hsame_symm reprEmpty)))
        (And.intro
          (And.intro reprCentral
            (hsame_trans emptyLefts.right.right.right (hsame_symm reprEmpty)))
          (And.intro reprCentral
            (hsame_trans emptyClassified.right.left.right (hsame_symm reprEmpty)))))
  · intro carriers
    have emptyCarriers :
        CentralizerCosetCarrier mul a BHist.Empty l /\
          CentralizerCosetCarrier mul a BHist.Empty h /\
            CentralizerCosetCarrier mul a BHist.Empty r := by
      exact And.intro (And.intro emptyCentral (hsame_trans carriers.left.right reprEmpty))
        (And.intro (And.intro emptyCentral (hsame_trans carriers.right.left.right reprEmpty))
          (And.intro emptyCentral (hsame_trans carriers.right.right.left.right reprEmpty)))
    have emptyK : CentralizerCosetCarrier mul a BHist.Empty k :=
      And.intro emptyCentral (hsame_trans carriers.right.right.right.right reprEmpty)
    have emptyLeft : CentralizerCosetCarrier mul a BHist.Empty (append l (append h r)) :=
      Iff.mpr emptyContext emptyCarriers
    have sameLeftK : hsame (append l (append h r)) k :=
      hsame_trans emptyLeft.right (hsame_symm emptyK.right)
    exact Iff.mpr classifierTransport
      (And.intro emptyLeft (And.intro emptyK sameLeftK))

end BEDC.Derived.QuotientGroupUp
