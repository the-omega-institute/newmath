import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_triangle_readback_lock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      triangleAligned windowSeal readbackLock endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont triangle dyadic triangleAligned ->
        Cont triangleAligned windows windowSeal ->
          Cont windowSeal readback readbackLock ->
            Cont readbackLock realSeal endpoint ->
              PkgSig bundle endpoint pkg ->
                UnaryHistory triangle ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                  UnaryHistory readback ∧ UnaryHistory triangleAligned ∧
                    UnaryHistory windowSeal ∧ UnaryHistory readbackLock ∧
                      UnaryHistory realSeal ∧ UnaryHistory endpoint ∧
                        Cont triangle dyadic triangleAligned ∧
                          Cont triangleAligned windows windowSeal ∧
                            Cont windowSeal readback readbackLock ∧
                              Cont readbackLock realSeal endpoint ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier triangleDyadicAligned alignedWindowsSeal windowSealReadbackLock
    readbackLockRealSealEndpoint endpointPkg
  obtain ⟨_diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have triangleAlignedUnary : UnaryHistory triangleAligned :=
    unary_cont_closed triangleUnary dyadicUnary triangleDyadicAligned
  have windowSealUnary : UnaryHistory windowSeal :=
    unary_cont_closed triangleAlignedUnary windowsUnary alignedWindowsSeal
  have readbackLockUnary : UnaryHistory readbackLock :=
    unary_cont_closed windowSealUnary readbackUnary windowSealReadbackLock
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackLockUnary realSealUnary readbackLockRealSealEndpoint
  exact
    ⟨triangleUnary, dyadicUnary, windowsUnary, readbackUnary, triangleAlignedUnary,
      windowSealUnary, readbackLockUnary, realSealUnary, endpointUnary,
      triangleDyadicAligned, alignedWindowsSeal, windowSealReadbackLock,
      readbackLockRealSealEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
