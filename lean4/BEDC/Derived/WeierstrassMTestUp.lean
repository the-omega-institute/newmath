import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.WeierstrassMTestUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def WeierstrassMTestCarrier [AskSetup] [PackageSetup]
    (family majorant domination tail regseq realSeal transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory family ∧ UnaryHistory majorant ∧ UnaryHistory domination ∧
    UnaryHistory tail ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont family majorant domination ∧ Cont domination tail regseq ∧
          Cont regseq realSeal transport ∧ Cont transport route provenance ∧
            PkgSig bundle route pkg ∧ PkgSig bundle name pkg

theorem WeierstrassMTestCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {family majorant domination tail regseq realSeal transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport route
        provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport
            route provenance name bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport
            route provenance name bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport
            route provenance name bundle pkg ∧ hsame row provenance)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro provenance (And.intro carrier (hsame_refl provenance))
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

end BEDC.Derived.WeierstrassMTestUp
