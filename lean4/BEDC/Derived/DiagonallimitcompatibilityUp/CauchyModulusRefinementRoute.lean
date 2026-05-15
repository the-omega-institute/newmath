import BEDC.Derived.CauchyModulusRefinementUp
import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_cauchy_modulus_refinement_route [AskSetup]
    [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      m0 m1 u v t w q e h c p n terminal refinementRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      BEDC.Derived.CauchyModulusRefinementUp.CauchyModulusRefinementCarrier
          m0 m1 u v t w q e h c p n bundle pkg ->
        Cont readback realSeal terminal ->
          Cont terminal m0 refinementRead ->
            PkgSig bundle terminal pkg ->
              PkgSig bundle refinementRead pkg ->
                UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory terminal ∧
                  UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
                    UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧
                      UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
                        UnaryHistory refinementRead ∧ Cont readback realSeal terminal ∧
                          Cont terminal m0 refinementRead ∧ Cont m0 m1 u ∧ Cont u v t ∧
                            Cont t w q ∧ Cont q e h ∧ PkgSig bundle provenance pkg ∧
                              PkgSig bundle p pkg ∧ hsame h n ∧
                                PkgSig bundle terminal pkg ∧
                                  PkgSig bundle refinementRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg UnaryHistory
  intro diagonalCarrier refinementCarrier readbackRealSealTerminal terminalRefinementRead
    terminalPkg refinementPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := diagonalCarrier
  obtain ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary,
    hUnary, cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩ :=
    refinementCarrier
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealTerminal
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed terminalUnary m0Unary terminalRefinementRead
  exact
    ⟨readbackUnary, realSealUnary, terminalUnary, m0Unary, m1Unary, uUnary, vUnary,
      tUnary, wUnary, qUnary, eUnary, hUnary, cUnary, pUnary, nUnary,
      refinementReadUnary, readbackRealSealTerminal, terminalRefinementRead, m0m1u, uvt,
      twq, qeh, provenancePkg, pPkg, hn, terminalPkg, refinementPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
