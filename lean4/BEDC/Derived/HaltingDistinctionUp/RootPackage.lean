import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionNameCertRootPackage [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert auditRead routeRead
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont cert provenance auditRead →
        Cont classifier route routeRead →
          Cont routeRead diagonal endpoint →
            PkgSig bundle auditRead pkg →
              PkgSig bundle endpoint pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row cert ∧
                        HaltingDistinctionCarrier question trace diagonal halt classifier route
                          provenance cert bundle pkg)
                    (fun row : BHist =>
                      hsame row cert ∧ UnaryHistory question ∧ UnaryHistory trace ∧
                        UnaryHistory diagonal)
                    (fun row : BHist => hsame row cert ∧ PkgSig bundle provenance pkg)
                    hsame ∧
                  UnaryHistory routeRead ∧ UnaryHistory endpoint ∧
                    Cont classifier route routeRead ∧ Cont routeRead diagonal endpoint ∧
                      PkgSig bundle auditRead pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier certProvenanceAudit classifierRouteRead routeReadDiagonalEndpoint auditPkg
    endpointPkg
  have carrierFull :
      HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg :=
    carrier
  obtain ⟨_questionUnary, _traceUnary, diagonalUnary, _haltUnary, classifierUnary, routeUnary,
    _provenanceUnary, _certUnary, _questionTraceDiagonal, _diagonalHaltClassifier,
    _classifierRouteCert, _provenancePkg⟩ := carrier
  have obligations :=
    HaltingDistinctionNameCertObligations (question := question) (trace := trace)
      (diagonal := diagonal) (halt := halt) (classifier := classifier) (route := route)
      (provenance := provenance) (cert := cert) (auditRead := auditRead) (bundle := bundle)
      (pkg := pkg) carrierFull certProvenanceAudit auditPkg
  have semanticCert := obligations.left
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed classifierUnary routeUnary classifierRouteRead
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeReadUnary diagonalUnary routeReadDiagonalEndpoint
  exact
    ⟨semanticCert, routeReadUnary, endpointUnary, classifierRouteRead,
      routeReadDiagonalEndpoint, auditPkg, endpointPkg⟩

end BEDC.Derived.HaltingDistinctionUp
