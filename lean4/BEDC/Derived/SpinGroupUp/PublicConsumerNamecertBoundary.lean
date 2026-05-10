import BEDC.Derived.SpinGroupUp

namespace BEDC.Derived.SpinGroupUp

open BEDC.Derived.GroupUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SpinGroupRootCarrier_public_consumer_namecert_boundary [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row spinEndpoint)
          (fun row : BHist => hsame row spinEndpoint)
          (fun row : BHist => hsame row spinEndpoint) hsame ∧
        UnaryHistory unit ∧ UnaryHistory product ∧ GroupSingletonCarrier groupWord ∧
          Cont cliffordEndpoint groupWord spinEndpoint ∧ PkgSig bundle ledger pkg := by
  intro carrier
  have coverage := SpinGroupRootCarrier_public_consumer_boundary_coverage carrier
  have spinSelf : hsame spinEndpoint spinEndpoint :=
    hsame_refl spinEndpoint
  have cert :
      SemanticNameCert (fun row : BHist => hsame row spinEndpoint)
          (fun row : BHist => hsame row spinEndpoint)
          (fun row : BHist => hsame row spinEndpoint) hsame := {
    core := {
      carrier_inhabited := Exists.intro spinEndpoint spinSelf
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
    And.intro cert
      (And.intro coverage.left
        (And.intro coverage.right.right.left
          (And.intro coverage.right.right.right.right.right.left
            (And.intro coverage.right.right.right.right.right.right.right.right.right.left
              coverage.right.right.right.right.right.right.right.right.right.right))))

end BEDC.Derived.SpinGroupUp
