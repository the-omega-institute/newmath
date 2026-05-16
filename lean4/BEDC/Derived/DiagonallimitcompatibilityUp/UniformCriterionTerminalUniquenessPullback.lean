import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.UniformCauchyCriterionUp

theorem DiagonalLimitUniformCriterionTerminalUniquenessPullback [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      index modulus uTrans uRoutes uProv uName selector locked uniquenessRead uniformTerminal
      uniquenessTerminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      UniformCauchyCriterionPacket index windows modulus dyadic readback realSeal uTrans uRoutes
        uProv uName bundle pkg ->
        Cont dyadic windows readback ->
          Cont readback realSeal uniformTerminal ->
            Cont diagonal dyadic selector ->
              Cont selector windows locked ->
                Cont locked readback uniquenessRead ->
                  Cont readback realSeal uniquenessTerminal ->
                    PkgSig bundle uniformTerminal pkg ->
                      PkgSig bundle uniquenessTerminal pkg ->
                        UnaryHistory uniformTerminal ∧ UnaryHistory uniquenessTerminal ∧
                          hsame uniformTerminal uniquenessTerminal ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle uName pkg ∧
                              PkgSig bundle uniformTerminal pkg ∧
                                PkgSig bundle uniquenessTerminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory hsame
  intro carrier packet _dyadicWindowsReadback readbackRealSealUniform
    _diagonalDyadicSelector _selectorWindowsLocked _lockedReadbackUniqueness
    readbackRealSealUniqueness uniformPkg uniquenessPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _carrierDyadicWindowsReadback,
    _carrierReadbackRealSeal, _routeCertTransport, provenancePkg⟩ := carrier
  obtain ⟨_indexUnary, _windowsUnary', _modulusUnary, _dyadicUnary', _readbackUnary',
    _realSealUnary', _uTransUnary, _uRoutesUnary, _uProvUnary, _uNameUnary,
    _indexWindowsModulus, _modulusDyadicReadback, _readbackRealSealUTrans,
    _uTransRoutesProv, uNamePkg⟩ := packet
  have uniformUnary : UnaryHistory uniformTerminal :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealUniform
  have uniquenessUnary : UnaryHistory uniquenessTerminal :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealUniqueness
  have sameTerminals : hsame uniformTerminal uniquenessTerminal :=
    cont_respects_hsame (hsame_refl readback) (hsame_refl realSeal)
      readbackRealSealUniform readbackRealSealUniqueness
  exact
    ⟨uniformUnary, uniquenessUnary, sameTerminals, provenancePkg, uNamePkg,
      uniformPkg, uniquenessPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
