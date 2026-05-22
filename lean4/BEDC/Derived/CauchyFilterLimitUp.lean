import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyFilterLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyFilterLimitCarrier [AskSetup] [PackageSetup]
    (basis filter window readback tolerance sealRow transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory basis ∧ UnaryHistory filter ∧ UnaryHistory window ∧
    UnaryHistory readback ∧ UnaryHistory tolerance ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont basis filter window ∧ Cont window readback tolerance ∧
          Cont tolerance sealRow transport ∧ Cont transport route provenance ∧
            Cont sealRow provenance name ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg

theorem CauchyFilterLimitCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {basis filter window readback tolerance sealRow transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterLimitCarrier basis filter window readback tolerance sealRow transport route
        provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyFilterLimitCarrier basis filter window readback tolerance sealRow transport route
              provenance name bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          CauchyFilterLimitCarrier basis filter window readback tolerance sealRow transport route
              provenance name bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          CauchyFilterLimitCarrier basis filter window readback tolerance sealRow transport route
              provenance name bundle pkg ∧ hsame row sealRow)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRow (And.intro carrier (hsame_refl sealRow))
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
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

end BEDC.Derived.CauchyFilterLimitUp
