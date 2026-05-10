import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_root_operation_source_continuity_coupling
    {group topology product inverse neighborhood ledger provenance product' inverse' ledger' :
      BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      hsame product product' ->
        hsame inverse inverse' ->
          Cont product' inverse' ledger' ->
            TopGroupRootThresholdPackage group topology product' inverse' neighborhood ledger'
                provenance ∧
              hsame ledger ledger' ∧ hsame provenance ledger' := by
  intro package sameProduct sameInverse transportedLedger
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameProduct sameInverse
      package.right.right.right.right.right.left transportedLedger
  have transportedProduct : hsame product' (append group topology) :=
    hsame_trans (hsame_symm sameProduct) package.right.right.right.left
  have transportedInverse : hsame inverse' BHist.Empty :=
    hsame_trans (hsame_symm sameInverse) package.right.right.right.right.left
  have transportedProvenance : hsame provenance ledger' :=
    hsame_trans package.right.right.right.right.right.right sameLedger
  have transportedPackage :
      TopGroupRootThresholdPackage group topology product' inverse' neighborhood ledger'
        provenance :=
    And.intro package.left
      (And.intro package.right.left
        (And.intro package.right.right.left
          (And.intro transportedProduct
            (And.intro transportedInverse
              (And.intro transportedLedger transportedProvenance)))))
  exact And.intro transportedPackage (And.intro sameLedger transportedProvenance)

end BEDC.Derived.TopGroupUp
