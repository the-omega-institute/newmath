import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem TopGroupRootThresholdPackage_source_rows_empty_coupled
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      hsame (append group topology) BHist.Empty ∧ hsame (append product inverse) BHist.Empty ∧
        hsame (append ledger provenance) BHist.Empty ∧ hsame provenance BHist.Empty := by
  intro package
  have sourceEmpty : hsame (append group topology) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro package.left package.right.left)
  have productEmpty : hsame product BHist.Empty :=
    hsame_trans package.right.right.right.left sourceEmpty
  have productInverseEmpty : hsame (append product inverse) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro productEmpty package.right.right.right.right.left)
  have ledgerEmpty : hsame ledger BHist.Empty :=
    hsame_trans package.right.right.right.right.right.left productInverseEmpty
  have provenanceEmpty : hsame provenance BHist.Empty :=
    hsame_trans package.right.right.right.right.right.right ledgerEmpty
  have ledgerProvenanceEmpty : hsame (append ledger provenance) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro ledgerEmpty provenanceEmpty)
  exact And.intro sourceEmpty
    (And.intro productInverseEmpty (And.intro ledgerProvenanceEmpty provenanceEmpty))

end BEDC.Derived.TopGroupUp
