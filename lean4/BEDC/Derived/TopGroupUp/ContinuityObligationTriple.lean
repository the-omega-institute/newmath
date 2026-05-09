import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def TopGroupBHistContinuityObligationTriple
    (product inverse neighborhood productLedger inverseLedger ledger : BHist) : Prop :=
  Cont product neighborhood productLedger ∧ Cont inverse neighborhood inverseLedger ∧
    Cont product inverse ledger

theorem TopGroupBHistContinuityObligationTriple_sound
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger :
      BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          TopGroupBHistContinuityObligationTriple product inverse neighborhood productLedger
              inverseLedger ledger ∧
            UnaryHistory productLedger ∧ UnaryHistory inverseLedger := by
  intro package productLedgerCont inverseLedgerCont
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed boundary.right.right.left boundary.right.right.right.right.left
      productLedgerCont
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed boundary.right.right.right.left boundary.right.right.right.right.left
      inverseLedgerCont
  exact And.intro
    (And.intro productLedgerCont
      (And.intro inverseLedgerCont package.right.right.right.right.right.left))
    (And.intro productLedgerUnary inverseLedgerUnary)

end BEDC.Derived.TopGroupUp
