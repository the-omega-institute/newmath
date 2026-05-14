import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitSealCarrier_public_route_transport [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transport provenance localCert endpoint source'
      schedule' dyadic' diagonal' sealRow' transport' provenance' localCert' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transport provenance
        localCert endpoint bundle pkg ->
      hsame source source' ->
        hsame schedule schedule' ->
          hsame diagonal diagonal' ->
            hsame transport transport' ->
              hsame localCert localCert' ->
                Cont source' schedule' dyadic' ->
                  Cont dyadic' diagonal' sealRow' ->
                    Cont sealRow' transport' provenance' ->
                      Cont provenance' localCert' endpoint' ->
                        hsame endpoint' (append provenance' localCert') ->
                          PkgSig bundle endpoint' pkg ->
                            CauchyLimitSealCarrier source' schedule' dyadic' diagonal'
                                sealRow' transport' provenance' localCert' endpoint' bundle
                                pkg ∧
                              hsame dyadic dyadic' ∧ hsame sealRow sealRow' ∧
                                hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sourceSame scheduleSame diagonalSame transportSame localCertSame
    sourceScheduleDyadic' dyadicDiagonalSeal' sealTransportProvenance'
    provenanceLocalEndpoint' sameEndpoint' endpointPkg'
  obtain ⟨sourceUnary, scheduleUnary, _dyadicUnary, diagonalUnary, _sealUnary,
    transportUnary, _provenanceUnary, localCertUnary, _endpointUnary,
    sourceScheduleDyadic, dyadicDiagonalSeal, sealTransportProvenance,
    provenanceLocalEndpoint, _sameEndpoint, _endpointPkg⟩ := carrier
  have sourceUnary' : UnaryHistory source' :=
    unary_transport sourceUnary sourceSame
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary scheduleSame
  have dyadicUnary' : UnaryHistory dyadic' :=
    unary_cont_closed sourceUnary' scheduleUnary' sourceScheduleDyadic'
  have diagonalUnary' : UnaryHistory diagonal' :=
    unary_transport diagonalUnary diagonalSame
  have sealUnary' : UnaryHistory sealRow' :=
    unary_cont_closed dyadicUnary' diagonalUnary' dyadicDiagonalSeal'
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary transportSame
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed sealUnary' transportUnary' sealTransportProvenance'
  have localCertUnary' : UnaryHistory localCert' :=
    unary_transport localCertUnary localCertSame
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed provenanceUnary' localCertUnary' provenanceLocalEndpoint'
  have dyadicSame : hsame dyadic dyadic' :=
    cont_respects_hsame sourceSame scheduleSame sourceScheduleDyadic sourceScheduleDyadic'
  have sealSame : hsame sealRow sealRow' :=
    cont_respects_hsame dyadicSame diagonalSame dyadicDiagonalSeal dyadicDiagonalSeal'
  have provenanceSame : hsame provenance provenance' :=
    cont_respects_hsame sealSame transportSame sealTransportProvenance
      sealTransportProvenance'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame provenanceSame localCertSame provenanceLocalEndpoint
      provenanceLocalEndpoint'
  exact
    ⟨⟨sourceUnary', scheduleUnary', dyadicUnary', diagonalUnary', sealUnary',
        transportUnary', provenanceUnary', localCertUnary', endpointUnary',
        sourceScheduleDyadic', dyadicDiagonalSeal', sealTransportProvenance',
        provenanceLocalEndpoint', sameEndpoint', endpointPkg'⟩,
      dyadicSame, sealSame, provenanceSame, endpointSame⟩

end BEDC.Derived.CauchyLimitSealUp
