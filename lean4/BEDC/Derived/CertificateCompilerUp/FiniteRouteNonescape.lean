import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_finite_route_nonescape
    [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert edge edge' finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerClassifier source target graph landing routes transport provenance cert edge
        edge' bundle pkg →
      Cont cert routes finalRead →
        PkgSig bundle finalRead pkg →
          UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
            UnaryHistory landing ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
              UnaryHistory finalRead ∧ hsame edge edge' ∧ Cont source graph landing ∧
                Cont graph edge landing ∧ Cont graph edge' landing ∧
                  Cont landing routes target ∧ Cont cert routes finalRead ∧
                    hsame cert (append provenance target) ∧ PkgSig bundle cert pkg ∧
                      PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro classifier certRoutesFinal finalPkg
  obtain ⟨carrier, _edgeUnary, _edgeUnary', edgeSame, graphEdgeLanding,
    graphEdgeLanding', landingRoutesTarget'⟩ := classifier
  obtain ⟨sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary,
    _transportUnary, provenanceUnary, _sourceGraphLanding, _landingRoutesTarget,
    provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have certUnary : UnaryHistory cert :=
    unary_cont_closed provenanceUnary targetUnary provenanceTargetCert
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed certUnary routesUnary certRoutesFinal
  exact
    ⟨sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary, provenanceUnary,
      finalUnary, edgeSame, _sourceGraphLanding, graphEdgeLanding, graphEdgeLanding',
      landingRoutesTarget', certRoutesFinal, certMatchesEndpoint, certPkg, finalPkg⟩

end BEDC.Derived.CertificateCompilerUp
