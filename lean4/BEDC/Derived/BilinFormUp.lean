import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BilinFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def BilinFormBHistObligationSurface
    (left right scalar additive endpoint scalarLedger ledger : BHist) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory scalar ∧ UnaryHistory additive ∧
    Cont left right endpoint ∧ Cont endpoint scalar scalarLedger ∧
      Cont scalarLedger additive ledger

theorem BilinFormBHistObligationSurface_carrier_classifier_obligations
    {left right scalar additive endpoint scalarLedger ledger endpoint' scalarLedger' ledger' : BHist} :
    BilinFormBHistObligationSurface left right scalar additive endpoint scalarLedger ledger ->
      hsame endpoint endpoint' ->
        Cont left right endpoint' ->
          Cont endpoint' scalar scalarLedger' ->
            Cont scalarLedger' additive ledger' ->
              BilinFormBHistObligationSurface left right scalar additive endpoint' scalarLedger' ledger' ∧
                UnaryHistory endpoint' ∧ UnaryHistory scalarLedger' ∧ UnaryHistory ledger' ∧
                  hsame endpoint endpoint' ∧ hsame scalarLedger scalarLedger' ∧
                    hsame ledger ledger' := by
  intro surface sameEndpoint endpointCont scalarLedgerCont ledgerCont
  have endpointUnary : UnaryHistory endpoint' :=
    unary_cont_closed surface.left surface.right.left endpointCont
  have scalarLedgerUnary : UnaryHistory scalarLedger' :=
    unary_cont_closed endpointUnary surface.right.right.left scalarLedgerCont
  have ledgerUnary : UnaryHistory ledger' :=
    unary_cont_closed scalarLedgerUnary surface.right.right.right.left ledgerCont
  have sameScalarLedger : hsame scalarLedger scalarLedger' :=
    cont_respects_hsame sameEndpoint (hsame_refl scalar)
      surface.right.right.right.right.right.left scalarLedgerCont
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameScalarLedger (hsame_refl additive)
      surface.right.right.right.right.right.right ledgerCont
  constructor
  · exact
      And.intro surface.left
        (And.intro surface.right.left
          (And.intro surface.right.right.left
            (And.intro surface.right.right.right.left
              (And.intro endpointCont
                (And.intro scalarLedgerCont ledgerCont)))))
  · exact
      And.intro endpointUnary
        (And.intro scalarLedgerUnary
          (And.intro ledgerUnary
            (And.intro sameEndpoint
              (And.intro sameScalarLedger sameLedger))))

end BEDC.Derived.BilinFormUp
