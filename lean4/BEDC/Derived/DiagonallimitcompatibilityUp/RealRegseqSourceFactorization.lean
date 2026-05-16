import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRealRegseqSourceFactorization [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      source readbackOut sealOut : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic source ->
        Cont source readback readbackOut ->
          Cont readbackOut realSeal sealOut ->
            PkgSig bundle sealOut pkg ->
              UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory readback ∧
                UnaryHistory realSeal ∧ UnaryHistory source ∧ UnaryHistory readbackOut ∧
                  UnaryHistory sealOut ∧ Cont diagonal dyadic source ∧
                    Cont source readback readbackOut ∧
                      Cont readbackOut realSeal sealOut ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle sealOut pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory
  intro carrier diagonalDyadicSource sourceReadbackOut readbackOutRealSeal sealOutPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory source :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicSource
  have readbackOutUnary : UnaryHistory readbackOut :=
    unary_cont_closed sourceUnary readbackUnary sourceReadbackOut
  have sealOutUnary : UnaryHistory sealOut :=
    unary_cont_closed readbackOutUnary realSealUnary readbackOutRealSeal
  exact
    ⟨diagonalUnary, dyadicUnary, readbackUnary, realSealUnary, sourceUnary,
      readbackOutUnary, sealOutUnary, diagonalDyadicSource, sourceReadbackOut,
      readbackOutRealSeal, provenancePkg, sealOutPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
