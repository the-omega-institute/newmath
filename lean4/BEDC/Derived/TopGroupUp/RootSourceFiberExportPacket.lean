import BEDC.Derived.TopGroupUp.ContinuityLedgerCoverage

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootSourceFiberExportPacket_exactness
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      exportLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger exportLedger ->
            SemanticNameCert (fun row : BHist => hsame row exportLedger)
                (fun row : BHist => hsame row exportLedger)
                (fun row : BHist => hsame row exportLedger) hsame ∧
              GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
                UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
                  UnaryHistory exportLedger ∧ hsame exportLedger (append productLedger inverseLedger) ∧
                    hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package productRow inverseRow exportRow
  have rows :=
    TopGroupRootThresholdPackage_operation_ledger_obligation package productRow inverseRow
      exportRow
  have exportSelf : hsame exportLedger exportLedger :=
    hsame_refl exportLedger
  have cert :
      SemanticNameCert (fun row : BHist => hsame row exportLedger)
          (fun row : BHist => hsame row exportLedger)
          (fun row : BHist => hsame row exportLedger) hsame := {
    core := {
      carrier_inhabited := Exists.intro exportLedger exportSelf
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        exact hsame_trans (hsame_symm sameRows) carrierRow
    }
    pattern_sound := by
      intro _row carrier
      exact carrier
    ledger_sound := by
      intro _row carrier
      exact carrier
  }
  exact And.intro cert
    (And.intro package.left
      (And.intro package.right.left
        (And.intro rows.left
          (And.intro rows.right.left
            (And.intro rows.right.right.left
              (And.intro exportRow
                (And.intro rows.right.right.right.right.left
                  rows.right.right.right.right.right)))))))

end BEDC.Derived.TopGroupUp
