import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootThresholdPackage_export_boundary
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      SemanticNameCert (fun row : BHist => hsame row provenance)
        (fun row : BHist => hsame row provenance) (fun row : BHist => hsame row provenance)
        hsame ∧ GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
          UnaryHistory product ∧ UnaryHistory inverse ∧ UnaryHistory neighborhood ∧
            UnaryHistory ledger ∧ hsame ledger (append product inverse) ∧ hsame provenance ledger ∧
              hsame (append provenance ledger) BHist.Empty := by
  intro package
  have boundary := TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have cert := (TopGroupRootThresholdPackage_export_boundary_certificate package).left
  have provenanceEmpty := (TopGroupRootThresholdPackage_export_boundary_certificate package).right
  have ledgerEmpty : hsame ledger BHist.Empty :=
    hsame_trans (hsame_symm package.right.right.right.right.right.right) provenanceEmpty
  have exportEmpty : hsame (append provenance ledger) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro provenanceEmpty ledgerEmpty)
  exact And.intro cert
    (And.intro boundary.left
      (And.intro boundary.right.left
        (And.intro boundary.right.right.left
          (And.intro boundary.right.right.right.left
            (And.intro boundary.right.right.right.right.left
              (And.intro boundary.right.right.right.right.right.left
                (And.intro boundary.right.right.right.right.right.right.left
                  (And.intro boundary.right.right.right.right.right.right.right
                    exportEmpty))))))))

end BEDC.Derived.TopGroupUp
