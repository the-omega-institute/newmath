import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootThresholdPackage_source_compatibility_obligation
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      SemanticNameCert (fun row : BHist => hsame row (append group topology))
          (fun row : BHist => hsame row (append group topology))
          (fun row : BHist => hsame row (append group topology)) hsame ∧
        GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
          Cont group topology product ∧ Cont product inverse ledger ∧
            hsame provenance ledger := by
  intro package
  have rows := TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have sourceSelf : hsame (append group topology) (append group topology) :=
    hsame_refl (append group topology)
  have cert :
      SemanticNameCert (fun row : BHist => hsame row (append group topology))
          (fun row : BHist => hsame row (append group topology))
          (fun row : BHist => hsame row (append group topology)) hsame := {
    core := {
      carrier_inhabited := Exists.intro (append group topology) sourceSelf
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other target sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other sameRO source
        exact hsame_trans (hsame_symm sameRO) source
    }
    pattern_sound := by
      intro row source
      exact source
    ledger_sound := by
      intro row source
      exact source
  }
  exact And.intro cert
    (And.intro rows.left
        (And.intro rows.right.left
          (And.intro package.right.right.right.left
          (And.intro package.right.right.right.right.right.left
            package.right.right.right.right.right.right))))

theorem TopGroupRootThresholdPackage_operation_continuity_obligation
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      exists productLedger inverseLedger : BHist,
        Cont product neighborhood productLedger ∧ Cont inverse neighborhood inverseLedger ∧
          UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧ Cont product inverse ledger ∧
            hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package
  have operationScope :=
    TopGroupRootThresholdPackage_operation_scope package
  cases operationScope with
  | intro productLedger productRows =>
      cases productRows with
      | intro inverseLedger rows =>
          exact Exists.intro productLedger
            (Exists.intro inverseLedger
              (And.intro rows.left
                (And.intro rows.right.left
                  (And.intro rows.right.right.left
                    (And.intro rows.right.right.right.left
                      (And.intro rows.right.right.right.right.left
                        (And.intro rows.right.right.right.right.right
                          package.right.right.right.right.right.right)))))))

end BEDC.Derived.TopGroupUp
