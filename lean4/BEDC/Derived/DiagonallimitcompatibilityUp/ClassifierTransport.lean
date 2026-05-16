import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem DiagonalLimitCompatibilityClassifierTransport [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      diagonal' triangle' dyadic' windows' realSeal' sealRow' readback' route' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      hsame diagonal diagonal' →
        hsame triangle triangle' →
          hsame dyadic dyadic' →
            hsame windows windows' →
              hsame realSeal realSeal' →
                Cont diagonal' triangle' sealRow' →
                  Cont dyadic' windows' readback' →
                    Cont readback' realSeal' route' →
                      hsame sealRow sealRow' ∧ hsame readback readback' ∧
                        hsame route route' := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame
  intro carrier sameDiagonal sameTriangle sameDyadic sameWindows sameRealSeal
    diagonalTriangleSeal' dyadicWindowsReadback' readbackRealSealRoute'
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute,
    _routeCertTransport, _provenancePkg⟩ := carrier
  have sameSealRow : hsame sealRow sealRow' :=
    cont_respects_hsame sameDiagonal sameTriangle diagonalTriangleSeal diagonalTriangleSeal'
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameDyadic sameWindows dyadicWindowsReadback dyadicWindowsReadback'
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameReadback sameRealSeal readbackRealSealRoute readbackRealSealRoute'
  exact ⟨sameSealRow, sameReadback, sameRoute⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
