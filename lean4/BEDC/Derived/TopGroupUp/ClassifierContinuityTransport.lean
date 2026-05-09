import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_classifier_continuity_transport
    {group topology product inverse neighborhood ledger provenance product' inverse'
      neighborhood' ledger' provenance' : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      hsame product product' ->
        hsame inverse inverse' ->
          hsame neighborhood neighborhood' ->
            Cont product' inverse' ledger' ->
              hsame provenance' ledger' ->
                TopGroupRootThresholdPackage group topology product' inverse' neighborhood' ledger'
                    provenance' ∧
                  hsame ledger ledger' ∧ UnaryHistory neighborhood' := by
  intro package sameProduct sameInverse sameNeighborhood ledgerCont' sameProvenance'
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameProduct sameInverse
      package.right.right.right.right.right.left ledgerCont'
  have neighborhoodUnary' : UnaryHistory neighborhood' :=
    unary_transport boundary.right.right.right.right.left sameNeighborhood
  have transportedPackage :
      TopGroupRootThresholdPackage group topology product' inverse' neighborhood' ledger'
        provenance' :=
    And.intro package.left
      (And.intro package.right.left
        (And.intro neighborhoodUnary'
          (And.intro (hsame_trans (hsame_symm sameProduct) package.right.right.right.left)
            (And.intro (hsame_trans (hsame_symm sameInverse)
                package.right.right.right.right.left)
              (And.intro ledgerCont' sameProvenance')))))
  exact And.intro transportedPackage (And.intro sameLedger neighborhoodUnary')

end BEDC.Derived.TopGroupUp
