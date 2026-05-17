import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_triangle_seal_interface [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      triangleAligned windowSeal sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont triangle dyadic triangleAligned →
        Cont triangleAligned windows windowSeal →
          Cont windowSeal sealRow sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory triangle ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                UnaryHistory sealRow ∧ UnaryHistory triangleAligned ∧
                  UnaryHistory windowSeal ∧ UnaryHistory sealRead ∧
                    Cont diagonal triangle sealRow ∧
                      Cont triangle dyadic triangleAligned ∧
                        Cont triangleAligned windows windowSeal ∧
                          Cont windowSeal sealRow sealRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier triangleDyadicAligned triangleWindowSeal windowSealRead sealReadPkg
  obtain ⟨_diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have triangleAlignedUnary : UnaryHistory triangleAligned :=
    unary_cont_closed triangleUnary dyadicUnary triangleDyadicAligned
  have windowSealUnary : UnaryHistory windowSeal :=
    unary_cont_closed triangleAlignedUnary windowsUnary triangleWindowSeal
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowSealUnary sealUnary windowSealRead
  exact
    ⟨triangleUnary, dyadicUnary, windowsUnary, sealUnary, triangleAlignedUnary,
      windowSealUnary, sealReadUnary, diagonalTriangleSeal, triangleDyadicAligned,
      triangleWindowSeal, windowSealRead, provenancePkg, sealReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
