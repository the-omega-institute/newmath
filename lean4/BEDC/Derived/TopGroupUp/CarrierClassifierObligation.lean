import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootThresholdPackage_carrier_classifier_obligation
    {group topology product inverse neighborhood ledger provenance classifierLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont provenance ledger classifierLedger ->
        SemanticNameCert (fun h : BHist => hsame h provenance)
          (fun h : BHist => hsame h provenance)
          (fun h : BHist => hsame h provenance)
          (fun left right : BHist => hsame left right ∧ hsame left provenance ∧
            hsame right provenance) ∧
          UnaryHistory classifierLedger ∧ hsame classifierLedger (append provenance ledger) ∧
            GroupSingletonCarrier group ∧ TopologySingletonCarrier topology := by
  intro package classifierLedgerRow
  have scope := TopGroupRootThreshold_carrier_scope package
  have ledgerScope := TopGroupRootThresholdPackage_continuity_ledger_scope package
  have provenanceUnary : UnaryHistory provenance :=
    ledgerScope.right.right.left
  have classifierLedgerUnary : UnaryHistory classifierLedger :=
    unary_cont_closed provenanceUnary ledgerScope.right.left classifierLedgerRow
  have provenanceSelf : hsame provenance provenance :=
    hsame_refl provenance
  have cert :
      SemanticNameCert (fun h : BHist => hsame h provenance)
        (fun h : BHist => hsame h provenance)
        (fun h : BHist => hsame h provenance)
        (fun left right : BHist => hsame left right ∧ hsame left provenance ∧
          hsame right provenance) := {
    core := {
      carrier_inhabited := Exists.intro provenance provenanceSelf
      equiv_refl := by
        intro row source
        exact And.intro (hsame_refl row) (And.intro source source)
      equiv_symm := by
        intro left right classified
        exact And.intro (hsame_symm classified.left)
          (And.intro classified.right.right classified.right.left)
      equiv_trans := by
        intro left middle right classifiedLM classifiedMR
        have sameLR : hsame left right :=
          hsame_trans classifiedLM.left classifiedMR.left
        exact And.intro sameLR
          (And.intro classifiedLM.right.left classifiedMR.right.right)
      carrier_respects_equiv := by
        intro left right classified _source
        exact classified.right.right
    }
    pattern_sound := by
      intro row source
      exact source
    ledger_sound := by
      intro row source
      exact source
  }
  exact
    And.intro cert
      (And.intro classifierLedgerUnary
        (And.intro classifierLedgerRow
          (And.intro scope.left scope.right.left)))

end BEDC.Derived.TopGroupUp
