import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilitySealReadbackExactness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sealReadback sealOutput : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal triangle sealRow →
        Cont dyadic windows readback →
          Cont readback realSeal sealReadback →
            Cont sealReadback sealRow sealOutput →
              PkgSig bundle sealOutput pkg →
                UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
                  UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                    UnaryHistory sealReadback ∧ UnaryHistory sealOutput ∧
                      Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
                        Cont readback realSeal sealReadback ∧
                          Cont sealReadback sealRow sealOutput ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle sealOutput pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalTriangleSeal dyadicWindowsReadback readbackRealSealReadback
    sealReadbackSealOutput sealOutputPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _carrierDiagonalTriangleSeal, _carrierDyadicWindowsReadback,
    _readbackRealSealRoute, _routeCertTransport, provenancePkg⟩ := carrier
  have sealReadbackUnary : UnaryHistory sealReadback :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealReadback
  have sealOutputUnary : UnaryHistory sealOutput :=
    unary_cont_closed sealReadbackUnary _sealRowUnary sealReadbackSealOutput
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary,
      sealReadbackUnary, sealOutputUnary, diagonalTriangleSeal, dyadicWindowsReadback,
      readbackRealSealReadback, sealReadbackSealOutput, provenancePkg, sealOutputPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
