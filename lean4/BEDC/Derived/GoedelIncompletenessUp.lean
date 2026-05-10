import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.GoedelIncompletenessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem GoedelIncompletenessFixedPointLedger_obligation
    {formula numbering proofChecker provability fixedPoint ledger : BHist} :
    UnaryHistory formula ->
      UnaryHistory numbering ->
        UnaryHistory proofChecker ->
          Cont formula numbering fixedPoint ->
            Cont proofChecker fixedPoint provability ->
              Cont fixedPoint provability ledger ->
                UnaryHistory fixedPoint ∧ UnaryHistory provability ∧ UnaryHistory ledger ∧
                  hsame fixedPoint (append formula numbering) ∧
                    hsame provability (append proofChecker fixedPoint) ∧
                      hsame ledger (append fixedPoint provability) := by
  intro formulaUnary numberingUnary proofCheckerUnary fixedPointRow provabilityRow ledgerRow
  have fixedPointUnary : UnaryHistory fixedPoint :=
    unary_cont_closed formulaUnary numberingUnary fixedPointRow
  have provabilityUnary : UnaryHistory provability :=
    unary_cont_closed proofCheckerUnary fixedPointUnary provabilityRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed fixedPointUnary provabilityUnary ledgerRow
  constructor
  · exact fixedPointUnary
  constructor
  · exact provabilityUnary
  constructor
  · exact ledgerUnary
  constructor
  · exact fixedPointRow
  constructor
  · exact provabilityRow
  · exact ledgerRow

end BEDC.Derived.GoedelIncompletenessUp
