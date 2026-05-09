import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.TopGroupUp
