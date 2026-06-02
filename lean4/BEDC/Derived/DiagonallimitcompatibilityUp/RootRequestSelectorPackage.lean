import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootRequestSelectorPackage [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      request selector sealPackage : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic request ->
        Cont request windows selector ->
          Cont selector realSeal sealPackage ->
            PkgSig bundle sealPackage pkg ->
              UnaryHistory request ∧ UnaryHistory selector ∧ UnaryHistory sealPackage ∧
                Cont diagonal dyadic request ∧ Cont request windows selector ∧
                  Cont selector realSeal sealPackage ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle sealPackage pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier diagonalDyadicRequest requestWindowsSelector selectorRealSealPackage
    sealPackagePkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have requestUnary : UnaryHistory request :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicRequest
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed requestUnary windowsUnary requestWindowsSelector
  have sealPackageUnary : UnaryHistory sealPackage :=
    unary_cont_closed selectorUnary realSealUnary selectorRealSealPackage
  exact
    ⟨requestUnary, selectorUnary, sealPackageUnary, diagonalDyadicRequest,
      requestWindowsSelector, selectorRealSealPackage, provenancePkg, sealPackagePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
