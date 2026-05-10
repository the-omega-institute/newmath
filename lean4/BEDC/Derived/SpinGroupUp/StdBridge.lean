import BEDC.Derived.SpinGroupUp

namespace BEDC.Derived.SpinGroupUp

open BEDC.Derived.CliffordUp
open BEDC.Derived.GroupUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem SpinGroupUp_StdBridge [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row spinEndpoint)
          (fun row : BHist => hsame row spinEndpoint)
          (fun row : BHist => hsame row spinEndpoint) hsame ∧
        CliffordCarrierPackage unit vector product boundary cliffordEndpoint ∧
          GroupSingletonCarrier groupWord ∧ Cont cliffordEndpoint groupWord spinEndpoint ∧
            PkgSig bundle ledger pkg := by
  intro carrier
  have sourceScope := SpinGroupRootCarrier_source_scope carrier
  have cert :
      SemanticNameCert (fun row : BHist => hsame row spinEndpoint)
          (fun row : BHist => hsame row spinEndpoint)
          (fun row : BHist => hsame row spinEndpoint) hsame := by
    constructor
    · constructor
      · exact Exists.intro spinEndpoint (hsame_refl spinEndpoint)
      · intro row _source
        exact hsame_refl row
      · intro _row _other sameRows
        exact hsame_symm sameRows
      · intro _row _other _third sameFirst sameSecond
        exact hsame_trans sameFirst sameSecond
      · intro _row _other sameRows rowSource
        exact hsame_trans (hsame_symm sameRows) rowSource
    · intro _row source
      exact source
    · intro _row source
      exact source
  exact And.intro cert
    (And.intro sourceScope.left
      (And.intro sourceScope.right.left
        (And.intro sourceScope.right.right.right.left sourceScope.right.right.right.right)))

end BEDC.Derived.SpinGroupUp
