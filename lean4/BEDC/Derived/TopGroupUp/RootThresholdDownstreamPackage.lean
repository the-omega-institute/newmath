import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

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

end BEDC.Derived.TopGroupUp
