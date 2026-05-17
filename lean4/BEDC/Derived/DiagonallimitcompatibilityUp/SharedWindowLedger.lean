import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.FKernel.Cont.Step

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilitySharedWindowLedger [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      alternateReadback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont dyadic windows alternateReadback →
        UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory alternateReadback ∧
          Cont dyadic windows readback ∧ Cont dyadic windows alternateReadback ∧
            hsame readback alternateReadback ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg UnaryHistory
  intro carrier alternateRoute
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have alternateUnary : UnaryHistory alternateReadback :=
    unary_cont_closed dyadicUnary windowsUnary alternateRoute
  have sameReadback : hsame readback alternateReadback :=
    cont_determinacy_up_to_hsame_spine dyadicWindowsReadback alternateRoute
  exact
    ⟨windowsUnary, readbackUnary, alternateUnary, dyadicWindowsReadback, alternateRoute,
      sameReadback, provenancePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
