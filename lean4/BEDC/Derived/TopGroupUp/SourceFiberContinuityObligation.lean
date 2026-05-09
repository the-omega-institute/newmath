import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_source_fiber_continuity_obligation
    {group topology product inverse neighborhood ledger provenance product' inverse'
      neighborhood' ledger' classifier' : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      hsame product product' ->
        hsame inverse inverse' ->
          hsame neighborhood neighborhood' ->
            Cont product' inverse' ledger' ->
              Cont ledger' neighborhood' classifier' ->
                hsame ledger ledger' ∧ UnaryHistory classifier' ∧
                  hsame classifier' (append ledger' neighborhood') ∧
                    hsame provenance ledger := by
  intro package sameProduct sameInverse sameNeighborhood ledgerCont classifierCont
  have stability :=
    TopGroupRootThresholdPackage_continuity_classifier_stability package sameProduct
      sameInverse ledgerCont
  have neighborhoodUnary' : UnaryHistory neighborhood' :=
    unary_transport
      (TopGroupRootThresholdPackage_source_coupled_continuity_boundary
        package).right.right.right.right.left
      sameNeighborhood
  have classifierUnary' : UnaryHistory classifier' :=
    unary_cont_closed stability.right.right.right neighborhoodUnary' classifierCont
  exact And.intro stability.left
    (And.intro classifierUnary'
      (And.intro classifierCont package.right.right.right.right.right.right))

theorem TopGroupRootSourceFiber_ledger_exactness
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      operationLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger operationLedger ->
            SemanticNameCert (fun row : BHist => hsame row operationLedger)
              (fun row : BHist => hsame row operationLedger)
              (fun row : BHist => hsame row operationLedger) hsame ∧
              UnaryHistory operationLedger ∧
                hsame operationLedger (append productLedger inverseLedger) ∧
                  hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package productRow inverseRow operationRow
  have operationRows :=
    TopGroupRootThresholdPackage_operation_ledger_obligation package productRow inverseRow
      operationRow
  have operationSelf : hsame operationLedger operationLedger :=
    hsame_refl operationLedger
  have cert :
      SemanticNameCert (fun row : BHist => hsame row operationLedger)
        (fun row : BHist => hsame row operationLedger)
        (fun row : BHist => hsame row operationLedger) hsame := {
    core := {
      carrier_inhabited := Exists.intro operationLedger operationSelf
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
      intro row carrier
      exact carrier
    ledger_sound := by
      intro row carrier
      exact carrier
  }
  exact And.intro cert
    (And.intro operationRows.right.right.left
      (And.intro operationRow
        (And.intro operationRows.right.right.right.right.left
          operationRows.right.right.right.right.right)))

end BEDC.Derived.TopGroupUp
