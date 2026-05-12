import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.LocatedCutUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

def LocatedCutCarrier [AskSetup] [PackageSetup]
    (lower upper window handoff sealRow transportRow route provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont lower upper window ∧
    Cont window handoff transportRow ∧
      Cont transportRow route provenance ∧
        Cont provenance localCert sealRow ∧
          PkgSig bundle provenance pkg ∧ hsame sealRow handoff ∧ hsame sealRow provenance

theorem LocatedCutCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
            bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
            bundle pkg ∧ hsame row handoff)
        (fun row : BHist =>
          LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
            bundle pkg ∧ hsame row provenance)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRow (And.intro carrier (hsame_refl sealRow))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact And.intro source.left
        (hsame_trans source.right source.left.right.right.right.right.right.left)
    ledger_sound := by
      intro _row source
      exact And.intro source.left
        (hsame_trans source.right source.left.right.right.right.right.right.right)
  }

end BEDC.Derived.LocatedCutUp
