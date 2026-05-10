import BEDC.Derived.TopGroupUp.ObligationInventory

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

def TopGroupObligationSurface
    (group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      consumerLedger carrierLedger classifierLedger : BHist) : Prop :=
  TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ∧
    Cont product neighborhood productLedger ∧ Cont inverse neighborhood inverseLedger ∧
      Cont productLedger inverseLedger consumerLedger ∧ Cont group neighborhood carrierLedger ∧
        Cont provenance ledger classifierLedger ∧ GroupSingletonCarrier group ∧
          TopologySingletonCarrier topology ∧ UnaryHistory product ∧ UnaryHistory inverse ∧
            UnaryHistory neighborhood ∧ UnaryHistory productLedger ∧
              UnaryHistory inverseLedger ∧ UnaryHistory consumerLedger ∧
                UnaryHistory carrierLedger ∧ UnaryHistory classifierLedger ∧
                  hsame product (append group topology) ∧ hsame inverse BHist.Empty ∧
                    hsame ledger (append product inverse) ∧ hsame provenance ledger ∧
                      hsame productLedger (append product neighborhood) ∧
                        hsame inverseLedger (append inverse neighborhood) ∧
                          hsame consumerLedger (append productLedger inverseLedger) ∧
                            hsame carrierLedger (append group neighborhood) ∧
                              hsame classifierLedger (append provenance ledger)

theorem TopGroupObligationSurface_public_consumer_exhaustion
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      consumerLedger carrierLedger classifierLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger consumerLedger ->
            Cont group neighborhood carrierLedger ->
              Cont provenance ledger classifierLedger ->
                TopGroupObligationSurface group topology product inverse neighborhood ledger
                  provenance productLedger inverseLedger consumerLedger carrierLedger
                  classifierLedger := by
  intro package productCont inverseCont consumerCont carrierCont classifierCont
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have ledgerScope :=
    TopGroupRootThresholdPackage_continuity_ledger_scope package
  have groupUnary : UnaryHistory group :=
    unary_transport unary_empty (hsame_symm package.left)
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed boundary.right.right.left boundary.right.right.right.right.left
      productCont
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed boundary.right.right.right.left boundary.right.right.right.right.left
      inverseCont
  have consumerLedgerUnary : UnaryHistory consumerLedger :=
    unary_cont_closed productLedgerUnary inverseLedgerUnary consumerCont
  have carrierLedgerUnary : UnaryHistory carrierLedger :=
    unary_cont_closed groupUnary boundary.right.right.right.right.left carrierCont
  have classifierLedgerUnary : UnaryHistory classifierLedger :=
    unary_cont_closed ledgerScope.right.right.left ledgerScope.right.left classifierCont
  exact And.intro package
    (And.intro productCont
      (And.intro inverseCont
        (And.intro consumerCont
          (And.intro carrierCont
            (And.intro classifierCont
              (And.intro package.left
                (And.intro package.right.left
                  (And.intro boundary.right.right.left
                    (And.intro boundary.right.right.right.left
                      (And.intro boundary.right.right.right.right.left
                        (And.intro productLedgerUnary
                          (And.intro inverseLedgerUnary
                            (And.intro consumerLedgerUnary
                              (And.intro carrierLedgerUnary
                                (And.intro classifierLedgerUnary
                                  (And.intro package.right.right.right.left
                                    (And.intro package.right.right.right.right.left
                                      (And.intro package.right.right.right.right.right.left
                                        (And.intro
                                          package.right.right.right.right.right.right
                                          (And.intro productCont
                                            (And.intro inverseCont
                                              (And.intro consumerCont
                                                (And.intro carrierCont
                                                  classifierCont)))))))))))))))))))))))

end BEDC.Derived.TopGroupUp
