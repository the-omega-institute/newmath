import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootThresholdPackage_obligation_inventory
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      carrierLedger classifierLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont group neighborhood carrierLedger ->
            Cont provenance ledger classifierLedger ->
              GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
                UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
                  UnaryHistory carrierLedger ∧ UnaryHistory classifierLedger ∧
                    Cont product inverse ledger ∧ hsame provenance ledger ∧
                      SemanticNameCert (fun h : BHist => hsame h provenance)
                        (fun h : BHist => hsame h provenance)
                        (fun h : BHist => hsame h provenance)
                        (fun left right : BHist =>
                          hsame left right ∧ hsame left provenance ∧
                            hsame right provenance) := by
  intro package productCont inverseCont carrierCont classifierCont
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have ledgerScope := TopGroupRootThresholdPackage_continuity_ledger_scope package
  have groupUnary : UnaryHistory group :=
    unary_transport unary_empty (hsame_symm package.left)
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed boundary.right.right.left boundary.right.right.right.right.left
      productCont
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed boundary.right.right.right.left boundary.right.right.right.right.left
      inverseCont
  have carrierLedgerUnary : UnaryHistory carrierLedger :=
    unary_cont_closed groupUnary boundary.right.right.right.right.left carrierCont
  have classifierLedgerUnary : UnaryHistory classifierLedger :=
    unary_cont_closed ledgerScope.right.right.left ledgerScope.right.left classifierCont
  have cert :
      SemanticNameCert (fun h : BHist => hsame h provenance)
        (fun h : BHist => hsame h provenance)
        (fun h : BHist => hsame h provenance)
        (fun left right : BHist =>
          hsame left right ∧ hsame left provenance ∧ hsame right provenance) := {
    core := {
      carrier_inhabited := Exists.intro provenance (hsame_refl provenance)
      equiv_refl := by
        intro h source
        exact And.intro (hsame_refl h) (And.intro source source)
      equiv_symm := by
        intro h k classified
        exact And.intro (hsame_symm classified.left)
          (And.intro classified.right.right classified.right.left)
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro (hsame_trans classifiedHK.left classifiedKR.left)
          (And.intro classifiedHK.right.left classifiedKR.right.right)
      carrier_respects_equiv := by
        intro h k classified _source
        exact classified.right.right
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro productLedgerUnary
        (And.intro inverseLedgerUnary
          (And.intro carrierLedgerUnary
            (And.intro classifierLedgerUnary
              (And.intro package.right.right.right.right.right.left
                (And.intro package.right.right.right.right.right.right cert)))))))

end BEDC.Derived.TopGroupUp
