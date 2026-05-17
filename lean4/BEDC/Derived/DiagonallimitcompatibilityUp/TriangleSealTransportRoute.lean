import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityTriangleSealTransportRoute [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      triangleAligned sealRead completion : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont triangle dyadic triangleAligned ->
        Cont triangleAligned windows sealRead ->
          Cont sealRead realSeal completion ->
            PkgSig bundle completion pkg ->
              UnaryHistory triangle ∧ UnaryHistory dyadic ∧ UnaryHistory triangleAligned ∧
                UnaryHistory windows ∧ UnaryHistory sealRead ∧ UnaryHistory realSeal ∧
                  UnaryHistory completion ∧ Cont triangle dyadic triangleAligned ∧
                    Cont triangleAligned windows sealRead ∧ Cont sealRead realSeal completion ∧
                      Cont route cert transport ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle completion pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle PkgSig
  intro carrier triangleDyadic triangleAlignedWindows sealReadRealSeal completionPkg
  obtain ⟨_diagonalUnary, triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have triangleAlignedUnary : UnaryHistory triangleAligned :=
    unary_cont_closed triangleUnary dyadicUnary triangleDyadic
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed triangleAlignedUnary windowsUnary triangleAlignedWindows
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed sealReadUnary realSealUnary sealReadRealSeal
  exact
    ⟨triangleUnary, dyadicUnary, triangleAlignedUnary, windowsUnary, sealReadUnary,
      realSealUnary, completionUnary, triangleDyadic, triangleAlignedWindows,
      sealReadRealSeal, routeCertTransport, provenancePkg, completionPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
