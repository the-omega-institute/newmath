import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_tail_schedule_readback [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      tailSchedule tailRoute endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      UnaryHistory tailSchedule →
        Cont sealRow tailSchedule tailRoute →
          Cont tailRoute readback endpoint →
            PkgSig bundle endpoint pkg →
              UnaryHistory sealRow ∧ UnaryHistory tailSchedule ∧ UnaryHistory tailRoute ∧
                UnaryHistory readback ∧ UnaryHistory endpoint ∧
                  Cont sealRow tailSchedule tailRoute ∧ Cont tailRoute readback endpoint ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier tailScheduleUnary sealTailRoute tailRouteReadback endpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have tailRouteUnary : UnaryHistory tailRoute :=
    unary_cont_closed sealUnary tailScheduleUnary sealTailRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed tailRouteUnary readbackUnary tailRouteReadback
  exact
    ⟨sealUnary, tailScheduleUnary, tailRouteUnary, readbackUnary, endpointUnary,
      sealTailRoute, tailRouteReadback, provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
