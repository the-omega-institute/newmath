import BEDC.Derived.TopGroupUp.ContinuityObligations

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_continuity_ledger_coverage
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger :
      BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          SemanticNameCert (fun row : BHist => hsame row (append productLedger inverseLedger))
            (fun row : BHist => hsame row (append productLedger inverseLedger))
            (fun row : BHist => hsame row (append productLedger inverseLedger)) hsame ∧
            UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
              hsame productLedger (append product neighborhood) ∧
                hsame inverseLedger (append inverse neighborhood) ∧ hsame provenance ledger := by
  intro package productLedgerCont inverseLedgerCont
  have rows :=
    TopGroupRootThresholdPackage_operation_continuity_witness_obligation package
      productLedgerCont inverseLedgerCont
  let continuityLedger := append productLedger inverseLedger
  have continuityLedgerSelf : hsame continuityLedger continuityLedger :=
    hsame_refl continuityLedger
  have cert :
      SemanticNameCert (fun row : BHist => hsame row continuityLedger)
        (fun row : BHist => hsame row continuityLedger)
        (fun row : BHist => hsame row continuityLedger) hsame := {
    core := {
      carrier_inhabited := Exists.intro continuityLedger continuityLedgerSelf
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
    (And.intro rows.left
      (And.intro rows.right.left
        (And.intro rows.right.right.left
          (And.intro rows.right.right.right.left
            rows.right.right.right.right.right))))

end BEDC.Derived.TopGroupUp
