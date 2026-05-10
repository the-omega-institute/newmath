import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_operation_continuity_ledger_scope
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      exists productLedger inverseLedger consumerLedger : BHist,
        Cont product neighborhood productLedger ∧ Cont inverse neighborhood inverseLedger ∧
          Cont productLedger inverseLedger consumerLedger ∧
            SemanticNameCert (fun row : BHist => hsame row consumerLedger)
              (fun row : BHist => hsame row consumerLedger)
              (fun row : BHist => hsame row consumerLedger) hsame ∧
              UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
                UnaryHistory consumerLedger ∧
                  hsame consumerLedger
                    (append (append product neighborhood) (append inverse neighborhood)) ∧
                    hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package
  have scope := TopGroupRootThresholdPackage_operation_scope package
  cases scope with
  | intro productLedger scopeTail =>
      cases scopeTail with
      | intro inverseLedger scopeRows =>
          let consumerLedger := append productLedger inverseLedger
          have consumerRow : Cont productLedger inverseLedger consumerLedger := by
            rfl
          have ledgerRows :=
            TopGroupRootThresholdPackage_operation_ledger_obligation package scopeRows.left
              scopeRows.right.left consumerRow
          have cert :
              SemanticNameCert (fun row : BHist => hsame row consumerLedger)
                (fun row : BHist => hsame row consumerLedger)
                (fun row : BHist => hsame row consumerLedger) hsame := {
            core := {
              carrier_inhabited := Exists.intro consumerLedger (hsame_refl consumerLedger)
              equiv_refl := by
                intro row _carrier
                exact hsame_refl row
              equiv_symm := by
                intro row row' same
                exact hsame_symm same
              equiv_trans := by
                intro row row' row'' sameRow sameRow'
                exact hsame_trans sameRow sameRow'
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
          exact Exists.intro productLedger
            (Exists.intro inverseLedger
              (Exists.intro consumerLedger
                (And.intro scopeRows.left
                  (And.intro scopeRows.right.left
                    (And.intro consumerRow
                      (And.intro cert ledgerRows))))))

end BEDC.Derived.TopGroupUp
