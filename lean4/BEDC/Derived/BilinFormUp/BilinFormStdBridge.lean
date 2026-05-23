import BEDC.Derived.BilinFormUp

namespace BEDC.Derived.BilinFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem BilinFormUp_StdBridge {left right scalar additive endpoint scalarLedger ledger : BHist} :
    BilinFormBHistObligationSurface left right scalar additive endpoint scalarLedger ledger →
      UnaryHistory endpoint ∧ UnaryHistory scalarLedger ∧ UnaryHistory ledger ∧
        Cont left right endpoint ∧ Cont endpoint scalar scalarLedger ∧
          Cont scalarLedger additive ledger := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont BilinFormBHistObligationSurface
  intro surface
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed surface.left surface.right.left surface.right.right.right.right.left
  have scalarLedgerUnary : UnaryHistory scalarLedger :=
    unary_cont_closed endpointUnary surface.right.right.left
      surface.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scalarLedgerUnary surface.right.right.right.left
      surface.right.right.right.right.right.right
  exact
    And.intro endpointUnary
      (And.intro scalarLedgerUnary
        (And.intro ledgerUnary
          (And.intro surface.right.right.right.right.left
            (And.intro surface.right.right.right.right.right.left
              surface.right.right.right.right.right.right))))

end BEDC.Derived.BilinFormUp
