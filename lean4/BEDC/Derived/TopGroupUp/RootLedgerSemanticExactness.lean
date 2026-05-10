import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_root_ledger_semantic_exactness
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      rootLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger rootLedger ->
            SemanticNameCert (fun h : BHist => hsame h rootLedger)
              (fun h : BHist => hsame h rootLedger)
              (fun h : BHist => hsame h rootLedger) hsame ∧
              Cont group topology product ∧ Cont product inverse ledger ∧
                UnaryHistory rootLedger ∧ hsame rootLedger (append productLedger inverseLedger) ∧
                  hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package productRow inverseRow rootRow
  have obligation :=
    TopGroupRootThresholdPackage_operation_ledger_obligation package productRow inverseRow rootRow
  have sourceRows := TopGroupRootThresholdPackage_shared_source_rows package
  have rootSelf : hsame rootLedger rootLedger :=
    hsame_refl rootLedger
  have cert :
      SemanticNameCert (fun h : BHist => hsame h rootLedger)
        (fun h : BHist => hsame h rootLedger)
        (fun h : BHist => hsame h rootLedger) hsame := {
    core := {
      carrier_inhabited := Exists.intro rootLedger rootSelf
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK carrierH
        exact hsame_trans (hsame_symm sameHK) carrierH
    }
    pattern_sound := by
      intro h carrier
      exact carrier
    ledger_sound := by
      intro h carrier
      exact carrier
  }
  exact And.intro cert
    (And.intro sourceRows.left
      (And.intro sourceRows.right.left
        (And.intro obligation.right.right.left
          (And.intro rootRow
            (And.intro obligation.right.right.right.right.left
              obligation.right.right.right.right.right)))))

end BEDC.Derived.TopGroupUp
