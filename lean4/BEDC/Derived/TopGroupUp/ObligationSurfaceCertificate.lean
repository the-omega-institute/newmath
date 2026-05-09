import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootThresholdPackage_obligation_surface_certificate
    {group topology product inverse neighborhood ledger provenance carrierLedger classifierLedger :
      BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont group neighborhood carrierLedger ->
        Cont provenance ledger classifierLedger ->
          SemanticNameCert (fun row : BHist => hsame row provenance)
              (fun row : BHist => hsame row provenance)
              (fun row : BHist => hsame row provenance)
              (fun left right : BHist =>
                hsame left right ∧ hsame left provenance ∧ hsame right provenance) ∧
            GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
              UnaryHistory carrierLedger ∧ UnaryHistory classifierLedger ∧
                Cont product inverse ledger ∧ hsame provenance ledger ∧
                  hsame carrierLedger (append group neighborhood) ∧
                    hsame classifierLedger (append provenance ledger) := by
  intro package carrierLedgerRow classifierLedgerRow
  have carrierScope := TopGroupRootThreshold_carrier_scope package
  have ledgerScope := TopGroupRootThresholdPackage_continuity_ledger_scope package
  have cert :
      SemanticNameCert (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance)
          (fun left right : BHist =>
            hsame left right ∧ hsame left provenance ∧ hsame right provenance) := {
    core := {
      carrier_inhabited := Exists.intro provenance (hsame_refl provenance)
      equiv_refl := by
        intro row rowCarrier
        exact And.intro (hsame_refl row) (And.intro rowCarrier rowCarrier)
      equiv_symm := by
        intro left right classified
        exact And.intro (hsame_symm classified.left)
          (And.intro classified.right.right classified.right.left)
      equiv_trans := by
        intro left middle right classifiedLM classifiedMR
        exact And.intro (hsame_trans classifiedLM.left classifiedMR.left)
          (And.intro classifiedLM.right.left classifiedMR.right.right)
      carrier_respects_equiv := by
        intro left right classified _leftCarrier
        exact classified.right.right
    }
    pattern_sound := by
      intro _row rowCarrier
      exact rowCarrier
    ledger_sound := by
      intro _row rowCarrier
      exact rowCarrier
  }
  have carrierLedgerUnary : UnaryHistory carrierLedger :=
    unary_cont_closed carrierScope.right.right.left carrierScope.right.right.right.right.left
      carrierLedgerRow
  have classifierLedgerUnary : UnaryHistory classifierLedger :=
    unary_cont_closed ledgerScope.right.right.left ledgerScope.right.left classifierLedgerRow
  exact And.intro cert
    (And.intro carrierScope.left
      (And.intro carrierScope.right.left
        (And.intro carrierLedgerUnary
          (And.intro classifierLedgerUnary
            (And.intro ledgerScope.left
              (And.intro ledgerScope.right.right.right
                (And.intro carrierLedgerRow classifierLedgerRow)))))))

end BEDC.Derived.TopGroupUp
