import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_public_consumer_minimality
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      consumerLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger consumerLedger ->
            SemanticNameCert (fun row : BHist => hsame row consumerLedger)
              (fun row : BHist => hsame row consumerLedger)
              (fun row : BHist => hsame row consumerLedger) hsame ∧
              GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
                UnaryHistory consumerLedger ∧
                  hsame consumerLedger (append productLedger inverseLedger) ∧
                    Cont product inverse ledger ∧ hsame provenance ledger := by
  intro package productRow inverseRow consumerRow
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have obligation :=
    TopGroupRootThresholdPackage_operation_ledger_obligation package productRow inverseRow
      consumerRow
  have consumerReadback : hsame consumerLedger (append productLedger inverseLedger) :=
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
        intro row other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row other third sameFirst sameSecond
        exact hsame_trans sameFirst sameSecond
      carrier_respects_equiv := by
        intro row other sameRows rowSource
        exact hsame_trans (hsame_symm sameRows) rowSource
    }
    pattern_sound := by
      intro row source
      exact source
    ledger_sound := by
      intro row source
      exact source
  }
  exact
    ⟨cert, boundary.left, boundary.right.left, obligation.right.right.left, consumerReadback,
      package.right.right.right.right.right.left, package.right.right.right.right.right.right⟩

end BEDC.Derived.TopGroupUp
