import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootSourceFiber_export_exactness_semantic_certificate
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
                    Cont product inverse ledger ∧ hsame ledger (append product inverse) ∧
                      hsame provenance ledger := by
  intro package productCont inverseCont exportCont
  have exportRows :=
    TopGroupRootSourceFiber_export_continuity package productCont inverseCont exportCont
  have commonRows :=
    TopGroupRootSourceFiber_export_common_cont_ledger package productCont inverseCont
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
        intro row row' same carrier
        exact hsame_trans (hsame_symm same) carrier
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
        (And.intro exportRows.left
          (And.intro exportRows.right.left
            (And.intro exportRows.right.right.left
              (And.intro exportRows.right.right.right.left
                (And.intro commonRows.left
                  (And.intro exportRows.right.right.right.right.left
                    exportRows.right.right.right.right.right))))))))

end BEDC.Derived.TopGroupUp
