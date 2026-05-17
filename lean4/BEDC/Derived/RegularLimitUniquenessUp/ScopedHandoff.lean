import BEDC.Derived.RegularLimitUniquenessUp

/-!
# RegularLimitUniquenessUp scoped handoff.
-/

namespace BEDC.Derived.RegularLimitUniquenessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularLimitUniquenessCarrier_scoped_handoff [AskSetup] [PackageSetup]
    {family diagonalLeft diagonalRight threshold readbackLeft readbackRight sealLeft sealRight
      separated transport route provenance localCert endpoint familyRead scopeRead auditRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLimitUniquenessCarrier family diagonalLeft diagonalRight threshold readbackLeft
        readbackRight sealLeft sealRight separated transport route provenance localCert endpoint
        bundle pkg ->
      Cont family threshold familyRead ->
        Cont separated localCert scopeRead ->
          Cont endpoint localCert auditRead ->
            PkgSig bundle familyRead pkg ->
              PkgSig bundle scopeRead pkg ->
                PkgSig bundle auditRead pkg ->
                  UnaryHistory familyRead /\ UnaryHistory scopeRead /\
                    UnaryHistory auditRead /\ PkgSig bundle familyRead pkg /\
                      PkgSig bundle scopeRead pkg /\ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier familyThresholdRead separatedLocalCertScope endpointLocalCertAudit familyReadPkg
    scopeReadPkg auditReadPkg
  obtain ⟨familyUnary, _diagonalLeftUnary, _diagonalRightUnary, thresholdUnary,
    readbackLeftUnary, readbackRightUnary, transportUnary, _routeUnary, _provenanceUnary,
    localCertUnary, _familyThresholdDiagonalLeft, _familyThresholdDiagonalRight,
    _diagonalLeftThresholdReadback, _diagonalRightThresholdReadback, readbackLeftThresholdSeal,
    readbackRightThresholdSeal, sealComparison, separatedTransportEndpoint,
    _routeProvenanceEndpoint, _endpointPkg⟩ := carrier
  have sealLeftUnary : UnaryHistory sealLeft :=
    unary_cont_closed readbackLeftUnary thresholdUnary readbackLeftThresholdSeal
  have sealRightUnary : UnaryHistory sealRight :=
    unary_cont_closed readbackRightUnary thresholdUnary readbackRightThresholdSeal
  have separatedUnary : UnaryHistory separated :=
    unary_cont_closed sealLeftUnary sealRightUnary sealComparison
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed separatedUnary transportUnary separatedTransportEndpoint
  have familyReadUnary : UnaryHistory familyRead :=
    unary_cont_closed familyUnary thresholdUnary familyThresholdRead
  have scopeReadUnary : UnaryHistory scopeRead :=
    unary_cont_closed separatedUnary localCertUnary separatedLocalCertScope
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed endpointUnary localCertUnary endpointLocalCertAudit
  exact
    ⟨familyReadUnary, scopeReadUnary, auditReadUnary, familyReadPkg, scopeReadPkg,
      auditReadPkg⟩

end BEDC.Derived.RegularLimitUniquenessUp
