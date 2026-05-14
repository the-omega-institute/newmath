import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_window_ledger_exactness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      triangleWindow sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont triangle windows triangleWindow →
        Cont triangleWindow readback sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory triangle ∧ UnaryHistory windows ∧ UnaryHistory triangleWindow ∧
              UnaryHistory readback ∧ UnaryHistory sealRead ∧
                Cont triangle windows triangleWindow ∧
                  Cont triangleWindow readback sealRead ∧ Cont dyadic windows readback ∧
                    Cont route cert transport ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory
  intro carrier triangleWindows triangleWindowReadback sealReadPkg
  obtain ⟨_diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have triangleWindowUnary : UnaryHistory triangleWindow :=
    unary_cont_closed triangleUnary windowsUnary triangleWindows
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed triangleWindowUnary readbackUnary triangleWindowReadback
  exact
    ⟨triangleUnary, windowsUnary, triangleWindowUnary, readbackUnary, sealReadUnary,
      triangleWindows, triangleWindowReadback, dyadicWindowsReadback, routeCertTransport,
      provenancePkg, sealReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
