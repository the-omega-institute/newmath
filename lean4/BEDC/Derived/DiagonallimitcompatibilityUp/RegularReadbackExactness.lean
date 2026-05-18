import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_regular_readback_exactness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      scheduledRead sealOut : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows scheduledRead ->
        Cont scheduledRead realSeal sealOut ->
          PkgSig bundle sealOut pkg ->
            hsame scheduledRead readback ∧ UnaryHistory sealOut ∧
              Cont scheduledRead realSeal sealOut ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle sealOut pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory
  intro carrier dyadicWindowsScheduled scheduledReadRealSeal sealOutPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have readbackScheduledRead : hsame readback scheduledRead :=
    cont_deterministic dyadicWindowsReadback dyadicWindowsScheduled
  have scheduledReadReadback : hsame scheduledRead readback :=
    hsame_symm readbackScheduledRead
  have scheduledReadUnary : UnaryHistory scheduledRead :=
    unary_transport readbackUnary readbackScheduledRead
  have sealOutUnary : UnaryHistory sealOut :=
    unary_cont_closed scheduledReadUnary realSealUnary scheduledReadRealSeal
  exact
    ⟨scheduledReadReadback, sealOutUnary, scheduledReadRealSeal, provenancePkg, sealOutPkg⟩

theorem DiagonalLimitCompatibilityRegularReadbackExactness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      triangleRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows triangleRead ->
        Cont triangleRead readback regularRead ->
          Cont regularRead realSeal sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                UnaryHistory realSeal ∧ UnaryHistory triangleRead ∧
                  UnaryHistory regularRead ∧ UnaryHistory sealRead ∧
                    Cont dyadic windows triangleRead ∧
                      Cont triangleRead readback regularRead ∧
                        Cont regularRead realSeal sealRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier dyadicWindowsTriangle triangleReadReadbackRegular regularReadRealSeal
    sealReadPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have triangleReadUnary : UnaryHistory triangleRead :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsTriangle
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed triangleReadUnary readbackUnary triangleReadReadbackRegular
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary realSealUnary regularReadRealSeal
  exact
    ⟨dyadicUnary, windowsUnary, readbackUnary, realSealUnary, triangleReadUnary,
      regularReadUnary, sealReadUnary, dyadicWindowsTriangle, triangleReadReadbackRegular,
      regularReadRealSeal, provenancePkg, sealReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
