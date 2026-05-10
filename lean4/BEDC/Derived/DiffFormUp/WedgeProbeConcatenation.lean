import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
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

theorem DiffFormWedgeProbeConcatenationLedger_semantic_name_certificate
    {left right : ProbeBundle BHist} {leftLedger rightLedger tensorLedger : BHist} :
    DiffFormWedgeProbeConcatenationLedger left right leftLedger rightLedger tensorLedger ->
      SemanticNameCert
        (fun endpoint : BHist =>
          DiffFormWedgeProbeConcatenationLedger left right leftLedger rightLedger endpoint)
        (fun endpoint : BHist =>
          DiffFormWedgeProbeConcatenationLedger left right leftLedger rightLedger endpoint)
        (fun endpoint : BHist =>
          DiffFormWedgeProbeConcatenationLedger left right leftLedger rightLedger endpoint)
        hsame := by
  intro ledger
  constructor
  · constructor
    · exact Exists.intro tensorLedger ledger
    · intro endpoint _carrier
      exact hsame_refl endpoint
    · intro endpoint endpoint' same
      exact hsame_symm same
    · intro endpoint endpoint' endpoint'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro endpoint endpoint' same carrier
      exact And.intro carrier.left
        (And.intro carrier.right.left
          (And.intro (unary_transport carrier.right.right.left same)
            (And.intro
              (hsame_trans (hsame_symm same) carrier.right.right.right.left)
              (And.intro carrier.right.right.right.right.left
                carrier.right.right.right.right.right))))
  · intro _endpoint source
    exact source
  · intro _endpoint source
    exact source

end BEDC.Derived.DiffFormUp
