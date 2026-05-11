import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ThetaFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ThetaFunctionCarrierSource [AskSetup] [PackageSetup]
    (period chart coeff provenance readback endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory period ∧ UnaryHistory chart ∧ UnaryHistory coeff ∧
    UnaryHistory provenance ∧ UnaryHistory readback ∧ UnaryHistory endpoint ∧
      Cont period chart coeff ∧ Cont provenance readback endpoint ∧
        PkgSig bundle endpoint pkg

theorem ThetaFunctionCarrierSource_namecert_boundary [AskSetup] [PackageSetup]
    {period chart coeff provenance readback endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ThetaFunctionCarrierSource period chart coeff provenance readback endpoint bundle pkg ->
      SemanticNameCert (fun h : BHist => hsame h endpoint)
          (fun h : BHist => hsame h endpoint) (fun h : BHist => hsame h endpoint)
          hsame ∧
        Cont period chart coeff ∧ Cont provenance readback endpoint ∧
          PkgSig bundle endpoint pkg := by
  intro source
  have cert :
      SemanticNameCert (fun h : BHist => hsame h endpoint)
          (fun h : BHist => hsame h endpoint) (fun h : BHist => hsame h endpoint)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact hsame_trans (hsame_symm sameRows) sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }
  exact And.intro cert
      (And.intro source.right.right.right.right.right.right.left
        (And.intro source.right.right.right.right.right.right.right.left
          source.right.right.right.right.right.right.right.right))

theorem ThetaFunctionCarrierSource_ledger_exactness [AskSetup] [PackageSetup]
    {period chart coeff provenance readback endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ThetaFunctionCarrierSource period chart coeff provenance readback endpoint bundle pkg ->
      UnaryHistory period ∧ UnaryHistory chart ∧ UnaryHistory coeff ∧
        Cont period chart coeff ∧ Cont provenance readback endpoint ∧
          PkgSig bundle endpoint pkg := by
  intro source
  exact And.intro source.left
    (And.intro source.right.left
      (And.intro source.right.right.left
        (And.intro source.right.right.right.right.right.right.left
          (And.intro source.right.right.right.right.right.right.right.left
            source.right.right.right.right.right.right.right.right))))

end BEDC.Derived.ThetaFunctionUp
