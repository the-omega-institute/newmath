import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_middle_row_handoff [AskSetup] [PackageSetup]
    {source middle target graphLeft landingLeft routesLeft transportLeft provenanceLeft
      certLeft graphRight landingRight routesRight transportRight provenanceRight certRight
      middleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source middle graphLeft landingLeft routesLeft transportLeft
        provenanceLeft certLeft bundle pkg ->
      CertificateCompilerCarrier middle target graphRight landingRight routesRight transportRight
          provenanceRight certRight bundle pkg ->
        hsame middleRead middle ->
          UnaryHistory middleRead ∧ Cont source graphLeft landingLeft ∧
            Cont landingLeft routesLeft middle ∧ Cont middle graphRight landingRight ∧
              Cont landingRight routesRight target ∧
                hsame certLeft (append provenanceLeft middle) ∧
                  hsame certRight (append provenanceRight target) ∧
                    PkgSig bundle certLeft pkg ∧ PkgSig bundle certRight pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle Pkg
  intro carrierLeft carrierRight middleReadSame
  obtain ⟨_sourceUnary, middleUnary, _graphLeftUnary, _landingLeftUnary, _routesLeftUnary,
    _transportLeftUnary, _provenanceLeftUnary, sourceGraphLeftLanding,
    landingLeftRoutesMiddle, _provenanceLeftMiddleCert, certLeftMatchesEndpoint,
    certLeftPkg⟩ := carrierLeft
  obtain ⟨_middleUnary, _targetUnary, _graphRightUnary, _landingRightUnary,
    _routesRightUnary, _transportRightUnary, _provenanceRightUnary,
    middleGraphRightLanding, landingRightRoutesTarget, _provenanceRightTargetCert,
    certRightMatchesEndpoint, certRightPkg⟩ := carrierRight
  have middleReadUnary : UnaryHistory middleRead :=
    unary_transport middleUnary (hsame_symm middleReadSame)
  exact
    ⟨middleReadUnary, sourceGraphLeftLanding, landingLeftRoutesMiddle,
      middleGraphRightLanding, landingRightRoutesTarget, certLeftMatchesEndpoint,
      certRightMatchesEndpoint, certLeftPkg, certRightPkg⟩

end BEDC.Derived.CertificateCompilerUp
