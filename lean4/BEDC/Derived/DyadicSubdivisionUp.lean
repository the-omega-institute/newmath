import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicSubdivisionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicSubdivisionSource [AskSetup] [PackageSetup]
    (parent level cells mesh validated provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory parent ∧ UnaryHistory level ∧ UnaryHistory cells ∧ UnaryHistory mesh ∧
    UnaryHistory validated ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
      Cont parent level cells ∧ Cont cells mesh validated ∧
        Cont validated provenance name ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle name pkg

theorem DyadicSubdivisionSource_namecert_obligations [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {parent level cells mesh validated provenance name : BHist} :
    DyadicSubdivisionSource parent level cells mesh validated provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          DyadicSubdivisionSource parent level cells mesh validated provenance name bundle pkg ∧
            hsame row validated)
        (fun row : BHist =>
          DyadicSubdivisionSource parent level cells mesh validated provenance name bundle pkg ∧
            hsame row validated)
        (fun row : BHist =>
          DyadicSubdivisionSource parent level cells mesh validated provenance name bundle pkg ∧
            hsame row validated)
        hsame := by
  intro sourceCarrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro validated (And.intro sourceCarrier (hsame_refl validated))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.DyadicSubdivisionUp
