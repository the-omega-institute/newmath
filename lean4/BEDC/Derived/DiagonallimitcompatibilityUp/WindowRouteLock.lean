import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityWindowRouteLock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      windowLocked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont windows route windowLocked →
      PkgSig bundle windowLocked pkg →
        UnaryHistory windows ∧ UnaryHistory route ∧ UnaryHistory windowLocked ∧
          Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
            Cont readback realSeal route ∧ Cont windows route windowLocked ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle windowLocked pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier windowsRouteLocked lockedPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have lockedUnary : UnaryHistory windowLocked :=
    unary_cont_closed windowsUnary routeUnary windowsRouteLocked
  exact
    ⟨windowsUnary, routeUnary, lockedUnary, diagonalTriangleSeal, dyadicWindowsReadback,
      readbackRealSealRoute, windowsRouteLocked, provenancePkg, lockedPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
