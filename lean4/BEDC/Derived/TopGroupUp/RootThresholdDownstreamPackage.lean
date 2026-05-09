import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

def TopGroupRootThresholdDownstreamPackage
    (group topology product inverse neighborhood classifier ledger provenance threshold :
      BHist) : Prop :=
  TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ∧
    hsame classifier (append group topology) ∧ Cont ledger classifier threshold ∧
      hsame threshold (append ledger classifier)

theorem TopGroupRootThresholdDownstreamPackage_boundary_rows
    {group topology product inverse neighborhood classifier ledger provenance threshold : BHist} :
    TopGroupRootThresholdDownstreamPackage group topology product inverse neighborhood classifier
        ledger provenance threshold ->
      GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory ledger ∧
        UnaryHistory classifier ∧ UnaryHistory threshold ∧ Cont ledger classifier threshold ∧
          hsame threshold (append ledger classifier) ∧ hsame provenance ledger := by
  intro downstream
  have package :=
    downstream.left
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have groupUnary : UnaryHistory group :=
    unary_transport unary_empty (hsame_symm package.left)
  have topologyUnary : UnaryHistory topology :=
    unary_transport unary_empty (hsame_symm package.right.left)
  have classifierUnaryRaw : UnaryHistory (append group topology) :=
    unary_append_closed groupUnary topologyUnary
  have classifierUnary : UnaryHistory classifier :=
    unary_transport classifierUnaryRaw (hsame_symm downstream.right.left)
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed boundary.right.right.right.right.right.left classifierUnary
      downstream.right.right.left
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro boundary.right.right.right.right.right.left
        (And.intro classifierUnary
          (And.intro thresholdUnary
            (And.intro downstream.right.right.left
              (And.intro downstream.right.right.right
                boundary.right.right.right.right.right.right.right))))))

theorem TopGroupRootThresholdPackage_root_threshold_namecert_threshold
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      SemanticNameCert (fun row : BHist => hsame row (append provenance ledger))
        (fun row : BHist => hsame row (append provenance ledger))
        (fun row : BHist => hsame row (append provenance ledger)) hsame ∧
        GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
          Cont product inverse ledger ∧ hsame provenance ledger := by
  intro package
  let threshold := append provenance ledger
  have thresholdSelf : hsame threshold threshold :=
    hsame_refl threshold
  have cert :
      SemanticNameCert (fun row : BHist => hsame row threshold)
        (fun row : BHist => hsame row threshold)
        (fun row : BHist => hsame row threshold) hsame := {
    core := {
      carrier_inhabited := Exists.intro threshold thresholdSelf
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
        intro row row' sameRows rowCarrier
        exact hsame_trans (hsame_symm sameRows) rowCarrier
    }
    pattern_sound := by
      intro row source
      exact source
    ledger_sound := by
      intro row source
      exact source
  }
  exact And.intro cert
    (And.intro package.left
      (And.intro package.right.left
        (And.intro package.right.right.right.right.right.left
          package.right.right.right.right.right.right)))

theorem TopGroupRootThresholdPackage_root_threshold_export_boundary
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      exportLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger exportLedger ->
            GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
              UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
                UnaryHistory exportLedger ∧ hsame exportLedger (append productLedger inverseLedger) ∧
                  hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package productLedgerRow inverseLedgerRow exportLedgerRow
  have boundary := TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed boundary.right.right.left boundary.right.right.right.right.left
      productLedgerRow
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed boundary.right.right.right.left boundary.right.right.right.right.left
      inverseLedgerRow
  have exportLedgerUnary : UnaryHistory exportLedger :=
    unary_cont_closed productLedgerUnary inverseLedgerUnary exportLedgerRow
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro productLedgerUnary
        (And.intro inverseLedgerUnary
          (And.intro exportLedgerUnary
            (And.intro exportLedgerRow
              (And.intro package.right.right.right.right.right.left
                package.right.right.right.right.right.right))))))

end BEDC.Derived.TopGroupUp
