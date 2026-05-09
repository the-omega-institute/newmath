import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_operation_ledger_semantic_certificate
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      consumerLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger consumerLedger ->
            SemanticNameCert (fun row : BHist => hsame row consumerLedger)
                (fun row : BHist => hsame row consumerLedger)
                (fun row : BHist => hsame row consumerLedger) hsame ∧
              UnaryHistory consumerLedger ∧
                hsame consumerLedger
                  (append (append product neighborhood) (append inverse neighborhood)) ∧
                  hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package productRow inverseRow consumerRow
  have rows :=
    TopGroupRootThresholdPackage_operation_ledger_obligation package productRow inverseRow
      consumerRow
  have cert :
      SemanticNameCert (fun row : BHist => hsame row consumerLedger)
        (fun row : BHist => hsame row consumerLedger)
        (fun row : BHist => hsame row consumerLedger) hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerLedger (hsame_refl consumerLedger)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _left _right same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _left _right same source
        exact hsame_trans (hsame_symm same) source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro rows.right.right.left
      (And.intro rows.right.right.right.left
        (And.intro rows.right.right.right.right.left rows.right.right.right.right.right)))

end BEDC.Derived.TopGroupUp
