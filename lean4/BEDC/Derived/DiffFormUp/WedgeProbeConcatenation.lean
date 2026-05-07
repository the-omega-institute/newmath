import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem DiffFormWedgeProbeConcatenation_classifier_stability
    {ScalarClassifier : BHist -> BHist -> Prop} {probes : ProbeBundle BHist}
    {d p t s a l d' p' t' s' a' l' e q u r b m e' q' u' r' b' m' : BHist} :
    DiffFormBHistClassifier ScalarClassifier probes d p t s a l d' p' t' s' a' l' ->
      DiffFormBHistClassifier ScalarClassifier probes e q u r b m e' q' u' r' b' m' ->
        hsame (append l m) (append l' m') := by
  intro leftRows rightRows
  cases leftRows.right.right.right.right.right.right.right
  cases rightRows.right.right.right.right.right.right.right
  rfl

def DiffFormWedgeProbeConcatenationLedger
    (left right : ProbeBundle BHist) (leftLedger rightLedger tensorLedger : BHist) : Prop :=
  UnaryHistory leftLedger ∧ UnaryHistory rightLedger ∧ UnaryHistory tensorLedger ∧
    hsame tensorLedger (append leftLedger rightLedger) ∧
      bundleLength (bundleAppend left right) = bundleLength left + bundleLength right ∧
        (forall probe : BHist,
          InBundle probe (bundleAppend left right) -> InBundle probe left ∨ InBundle probe right)

theorem DiffFormWedgeProbeConcatenationLedger_coverage
    {left right : ProbeBundle BHist} {leftLedger rightLedger tensorLedger : BHist} :
    DiffFormWedgeProbeConcatenationLedger left right leftLedger rightLedger tensorLedger ->
      bundleLength (bundleAppend left right) = bundleLength left + bundleLength right ∧
        (forall probe : BHist,
          InBundle probe (bundleAppend left right) <-> InBundle probe left ∨
            InBundle probe right) ∧
          UnaryHistory tensorLedger ∧ hsame tensorLedger (append leftLedger rightLedger) := by
  intro ledger
  exact And.intro (bundleLength_append left right)
    (And.intro
      (fun probe => inBundle_bundleAppend_iff (p := probe) (left := left) (right := right))
      (And.intro ledger.right.right.left ledger.right.right.right.left))

end BEDC.Derived.DiffFormUp
