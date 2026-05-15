import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_consumer_transport [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      diagonal' triangle' sealRow' dyadic' windows' readback' realSeal' transport' route'
      provenance' cert' endpoint endpoint' : BHist}
    {bundle bundle' : ProbeBundle ProbeName} {pkg pkg' : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      DiagonalLimitCompatibilityCarrier diagonal' triangle' sealRow' dyadic' windows' readback'
          realSeal' transport' route' provenance' cert' bundle' pkg' ->
        hsame readback readback' ->
          hsame realSeal realSeal' ->
            Cont readback realSeal endpoint ->
              Cont readback' realSeal' endpoint' ->
                PkgSig bundle endpoint pkg ->
                  PkgSig bundle' endpoint' pkg' ->
                    hsame endpoint endpoint' ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle' provenance' pkg' ∧ PkgSig bundle endpoint pkg ∧
                        PkgSig bundle' endpoint' pkg' := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle hsame
  intro carrier carrier' readbackSame realSealSame readbackRealSeal readbackRealSeal'
    endpointPkg endpointPkg'
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  obtain ⟨_diagonalUnary', _triangleUnary', _sealUnary', _dyadicUnary', _windowsUnary',
    _readbackUnary', _realSealUnary', _transportUnary', _routeUnary', _provenanceUnary',
    _certUnary', _diagonalTriangleSeal', _dyadicWindowsReadback', _readbackRealSealRoute',
    _routeCertTransport', provenancePkg'⟩ := carrier'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame readbackSame realSealSame readbackRealSeal readbackRealSeal'
  exact ⟨endpointSame, provenancePkg, provenancePkg', endpointPkg, endpointPkg'⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
