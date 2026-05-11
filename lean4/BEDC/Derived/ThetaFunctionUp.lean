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

def ThetaFunctionCarrier [AskSetup] [PackageSetup]
    (period chart coeff readback : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory period ∧ UnaryHistory chart ∧ UnaryHistory coeff ∧
    Cont period chart readback ∧ TokIntro bundle readback pkg

theorem ThetaFunctionCarrier_hsame_stability [AskSetup] [PackageSetup]
    {period chart coeff readback period' chart' coeff' readback' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg pkg' : Pkg} :
    ThetaFunctionCarrier period chart coeff readback bundle pkg ->
      TokIntro bundle readback' pkg' -> hsame period period' -> hsame chart chart' ->
        hsame coeff coeff' -> Cont period' chart' readback' ->
          ThetaFunctionCarrier period' chart' coeff' readback' bundle pkg' ∧
            hsame readback readback' ∧ psame bundle pkg pkg' := by
  intro source targetToken samePeriod sameChart sameCoeff targetCont
  have periodUnary : UnaryHistory period' :=
    unary_transport source.left samePeriod
  have chartUnary : UnaryHistory chart' :=
    unary_transport source.right.left sameChart
  have coeffUnary : UnaryHistory coeff' :=
    unary_transport source.right.right.left sameCoeff
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame samePeriod sameChart source.right.right.right.left targetCont
  have samePkg : psame bundle pkg pkg' :=
    psame.intro source.right.right.right.right targetToken sameReadback
  exact And.intro
    (And.intro periodUnary
      (And.intro chartUnary
        (And.intro coeffUnary
          (And.intro targetCont targetToken))))
    (And.intro sameReadback samePkg)

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

end BEDC.Derived.ThetaFunctionUp
