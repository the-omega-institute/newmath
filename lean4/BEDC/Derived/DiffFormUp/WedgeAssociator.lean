import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormWedgeDegreeLedger_associator_closure
    {d e f de ef leftOut rightOut leftLedger middleLedger rightLedger tensorLedger : BHist} :
    DiffFormWedgeDegreeLedger d e de leftLedger middleLedger tensorLedger ->
      DiffFormWedgeDegreeLedger de f leftOut leftLedger rightLedger tensorLedger ->
        DiffFormWedgeDegreeLedger e f ef middleLedger rightLedger tensorLedger ->
          DiffFormWedgeDegreeLedger d ef rightOut leftLedger rightLedger tensorLedger ->
            hsame leftOut rightOut ∧ UnaryHistory leftOut ∧ UnaryHistory rightOut := by
  intro leftPair leftParenthesized rightPair rightParenthesized
  have sameOut : hsame leftOut rightOut :=
    cont_assoc_unique leftPair.right.right.left rightPair.right.right.left
      leftParenthesized.right.right.left rightParenthesized.right.right.left
  exact And.intro sameOut
    (And.intro leftParenthesized.right.right.right.left rightParenthesized.right.right.right.left)

theorem DiffFormWedgeDegreeLedger_degree_additivity_transport
    {left right out leftLedger rightLedger tensorLedger left' right' out' : BHist} :
    DiffFormWedgeDegreeLedger left right out leftLedger rightLedger tensorLedger ->
      hsame left left' ->
        hsame right right' ->
          Cont left' right' out' ->
            DiffFormWedgeDegreeLedger left' right' out' leftLedger rightLedger tensorLedger ∧
              hsame out out' ∧ UnaryHistory out' := by
  intro ledger sameLeft sameRight outRow
  have sameOut : hsame out out' :=
    cont_respects_hsame sameLeft sameRight ledger.right.right.left outRow
  have transported :=
    DiffFormWedgeDegreeLedger_classifier_stability ledger sameLeft sameRight sameOut
  exact And.intro transported.left
    (And.intro sameOut transported.left.right.right.right.left)

end BEDC.Derived.DiffFormUp
