import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_downstream_boundary_sibling_link [AskSetup] [PackageSetup]
    {source middle target graph01 landing01 routes01 transport01 provenance01 cert01 graph12
      landing12 routes12 transport12 provenance12 cert12 boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source middle graph01 landing01 routes01 transport01
        provenance01 cert01 bundle pkg →
      CertificateCompilerCarrier middle target graph12 landing12 routes12 transport12
          provenance12 cert12 bundle pkg →
        Cont cert01 cert12 boundaryRead →
          PkgSig bundle boundaryRead pkg →
            UnaryHistory source ∧ UnaryHistory middle ∧ UnaryHistory target ∧
              UnaryHistory graph01 ∧ UnaryHistory graph12 ∧ UnaryHistory boundaryRead ∧
                Cont source graph01 landing01 ∧ Cont landing01 routes01 middle ∧
                  Cont middle graph12 landing12 ∧ Cont landing12 routes12 target ∧
                    Cont cert01 cert12 boundaryRead ∧ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro leftCarrier rightCarrier certBoundary boundaryPkg
  obtain ⟨sourceUnary, middleUnary, graphUnary01, _landingUnary01, _routesUnary01,
    _transportUnary01, provenanceUnary01, sourceGraphLanding01,
    landingRoutesMiddle, provenanceMiddleCert01, _certMatches01, _certPkg01⟩ :=
    leftCarrier
  obtain ⟨_middleUnaryRight, targetUnary, graphUnary12, _landingUnary12, _routesUnary12,
    _transportUnary12, provenanceUnary12, middleGraphLanding12, landingRoutesTarget,
    provenanceTargetCert12, _certMatches12, _certPkg12⟩ := rightCarrier
  have certUnary01 : UnaryHistory cert01 :=
    unary_cont_closed provenanceUnary01 middleUnary provenanceMiddleCert01
  have certUnary12 : UnaryHistory cert12 :=
    unary_cont_closed provenanceUnary12 targetUnary provenanceTargetCert12
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed certUnary01 certUnary12 certBoundary
  exact
    ⟨sourceUnary, middleUnary, targetUnary, graphUnary01, graphUnary12, boundaryUnary,
      sourceGraphLanding01, landingRoutesMiddle, middleGraphLanding12, landingRoutesTarget,
      certBoundary, boundaryPkg⟩

end BEDC.Derived.CertificateCompilerUp
