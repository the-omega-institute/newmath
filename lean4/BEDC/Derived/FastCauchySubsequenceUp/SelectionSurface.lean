import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FastCauchySubsequenceSelectionSurface [AskSetup] [PackageSetup]
    (S M Q F R W E H C P N selectorRead readbackRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ∧
    Cont M Q selectorRead ∧ Cont selectorRead F readbackRead ∧
      PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem FastCauchySubsequenceSelectionSurface_readback [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N selectorRead readbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceSelectionSurface S M Q F R W E H C P N selectorRead
        readbackRead bundle pkg ->
      UnaryHistory selectorRead ∧ UnaryHistory readbackRead ∧ Cont M Q selectorRead ∧
        Cont selectorRead F readbackRead := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro surface
  obtain ⟨carrier, selectorRoute, readbackRoute, _provenancePkg, _localNamePkg⟩ :=
    surface
  obtain ⟨_unaryS, unaryM, unaryQ, unaryF, _unaryR, _unaryW, _unaryE, _unaryH,
    _unaryC, _unaryP, _unaryN, _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed unaryM unaryQ selectorRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed selectorUnary unaryF readbackRoute
  exact ⟨selectorUnary, readbackUnary, selectorRoute, readbackRoute⟩

end BEDC.Derived.FastCauchySubsequenceUp
