import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootRouteTransportStability [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      diagonal' triangle' sealRow' dyadic' windows' readback' realSeal' transport' route'
      provenance' cert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      hsame diagonal diagonal' →
        hsame triangle triangle' →
          hsame dyadic dyadic' →
            hsame windows windows' →
              hsame readback readback' →
                hsame realSeal realSeal' →
                  hsame provenance provenance' →
                    hsame cert cert' →
                      Cont diagonal' triangle' sealRow' →
                        Cont dyadic' windows' readback' →
                          Cont readback' realSeal' route' →
                            Cont route' cert' transport' →
                              PkgSig bundle provenance' pkg →
                                DiagonalLimitCompatibilityCarrier diagonal' triangle' sealRow'
                                    dyadic' windows' readback' realSeal' transport' route'
                                    provenance' cert' bundle pkg ∧
                                  hsame sealRow sealRow' ∧ hsame route route' ∧
                                    hsame transport transport' := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  intro carrier sameDiagonal sameTriangle sameDyadic sameWindows sameReadback sameRealSeal
    sameProvenance sameCert diagonalTriangleSeal' dyadicWindowsReadback'
    readbackRealSealRoute' routeCertTransport' provenancePkg'
  obtain ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, transportUnary, routeUnary, provenanceUnary, certUnary,
    diagonalTriangleSeal, _dyadicWindowsReadback, readbackRealSealRoute,
    routeCertTransport, _provenancePkg⟩ := carrier
  have diagonalUnary' : UnaryHistory diagonal' :=
    unary_transport diagonalUnary sameDiagonal
  have triangleUnary' : UnaryHistory triangle' :=
    unary_transport triangleUnary sameTriangle
  have sealRowSame : hsame sealRow sealRow' :=
    cont_respects_hsame sameDiagonal sameTriangle diagonalTriangleSeal diagonalTriangleSeal'
  have sealRowUnary' : UnaryHistory sealRow' :=
    unary_transport sealRowUnary sealRowSame
  have dyadicUnary' : UnaryHistory dyadic' :=
    unary_transport dyadicUnary sameDyadic
  have windowsUnary' : UnaryHistory windows' :=
    unary_transport windowsUnary sameWindows
  have readbackUnary' : UnaryHistory readback' :=
    unary_transport readbackUnary sameReadback
  have realSealUnary' : UnaryHistory realSeal' :=
    unary_transport realSealUnary sameRealSeal
  have routeSame : hsame route route' :=
    cont_respects_hsame sameReadback sameRealSeal readbackRealSealRoute readbackRealSealRoute'
  have routeUnary' : UnaryHistory route' :=
    unary_transport routeUnary routeSame
  have certUnary' : UnaryHistory cert' :=
    unary_transport certUnary sameCert
  have transportSame : hsame transport transport' :=
    cont_respects_hsame routeSame sameCert routeCertTransport routeCertTransport'
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary transportSame
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  exact
    ⟨⟨diagonalUnary', triangleUnary', sealRowUnary', dyadicUnary', windowsUnary',
        readbackUnary', realSealUnary', transportUnary', routeUnary', provenanceUnary',
        certUnary', diagonalTriangleSeal', dyadicWindowsReadback', readbackRealSealRoute',
        routeCertTransport', provenancePkg'⟩,
      sealRowSame, routeSame, transportSame⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
