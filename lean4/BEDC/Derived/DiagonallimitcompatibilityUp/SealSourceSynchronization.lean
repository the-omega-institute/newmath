import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_seal_source_synchronization [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sealSource sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal triangle sealSource ->
        Cont sealSource dyadic sealRead ->
          PkgSig bundle sealRead pkg ->
            UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
              UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory sealSource ∧
                UnaryHistory sealRead ∧ Cont diagonal triangle sealSource ∧
                  Cont sealSource dyadic sealRead ∧ Cont dyadic windows readback ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalTriangleSource sourceDyadicRead sealReadPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sealSourceUnary : UnaryHistory sealSource :=
    unary_cont_closed diagonalUnary triangleUnary diagonalTriangleSource
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sealSourceUnary dyadicUnary sourceDyadicRead
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, readbackUnary,
      sealSourceUnary, sealReadUnary, diagonalTriangleSource, sourceDyadicRead,
      dyadicWindowsReadback, provenancePkg, sealReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
