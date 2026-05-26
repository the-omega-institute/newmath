import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_root_landing_consumer_determinacy
    [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert routeRead consumerRoute
      certEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg →
      hsame routeRead routes →
        Cont landing routeRead consumerRoute →
          hsame cert certEndpoint →
            PkgSig bundle consumerRoute pkg →
              SemanticNameCert
                (fun row : BHist =>
                  hsame row consumerRoute ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                (fun row : BHist =>
                  Cont landing routeRead row ∧ Cont source graph landing ∧
                    Cont landing routes target)
                (fun row : BHist =>
                  PkgSig bundle row pkg ∧ hsame certEndpoint (append provenance target) ∧
                    Cont provenance target cert)
                (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle Pkg SemanticNameCert
  intro carrier routeReadSame landingRouteConsumer certEndpointSame consumerPkg
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, landingUnary, routesUnary,
    _transportUnary, provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    provenanceTargetCert, certMatchesEndpoint, _certPkg⟩ := carrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_transport routesUnary (hsame_symm routeReadSame)
  have consumerRouteUnary : UnaryHistory consumerRoute :=
    unary_cont_closed landingUnary routeReadUnary landingRouteConsumer
  have certEndpointLedger : hsame certEndpoint (append provenance target) :=
    hsame_trans (hsame_symm certEndpointSame) certMatchesEndpoint
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRoute
          ⟨hsame_refl consumerRoute, consumerRouteUnary, consumerPkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _row' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      exact
        ⟨cont_result_hsame_transport landingRouteConsumer (hsame_symm sourceRow.left),
          sourceGraphLanding, landingRoutesTarget⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, certEndpointLedger, provenanceTargetCert⟩
  }

end BEDC.Derived.CertificateCompilerUp
