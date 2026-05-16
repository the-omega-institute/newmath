import BEDC.Derived.CauchyModulusRefinementUp
import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCauchyRefinementThresholdCorrespondence
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      m0 m1 u v t w q e h c p n terminal refinementRead comparison : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      BEDC.Derived.CauchyModulusRefinementUp.CauchyModulusRefinementCarrier
          m0 m1 u v t w q e h c p n bundle pkg →
        Cont readback realSeal terminal →
          Cont terminal m0 refinementRead →
            Cont windows v comparison →
              PkgSig bundle terminal pkg →
                PkgSig bundle refinementRead pkg →
                  PkgSig bundle comparison pkg →
                    UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                      UnaryHistory v ∧ UnaryHistory q ∧ UnaryHistory e ∧
                        UnaryHistory terminal ∧ UnaryHistory refinementRead ∧
                          UnaryHistory comparison ∧ Cont readback realSeal terminal ∧
                            Cont terminal m0 refinementRead ∧ Cont t w q ∧ Cont q e h ∧
                              Cont windows v comparison ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle p pkg ∧ PkgSig bundle terminal pkg ∧
                                  PkgSig bundle refinementRead pkg ∧
                                    PkgSig bundle comparison pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro diagonalCarrier refinementCarrier readbackTerminal terminalRefinement
    windowsComparison terminalPkg refinementPkg comparisonPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := diagonalCarrier
  obtain ⟨m0Unary, _m1Unary, _uUnary, vUnary, tUnary, wUnary, qUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, twq, qeh, pPkg, _hn⟩ :=
    refinementCarrier
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed readbackUnary realSealUnary readbackTerminal
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed terminalUnary m0Unary terminalRefinement
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed windowsUnary vUnary windowsComparison
  exact
    ⟨windowsUnary, readbackUnary, realSealUnary, vUnary, qUnary, eUnary, terminalUnary,
      refinementReadUnary, comparisonUnary, readbackTerminal, terminalRefinement, twq, qeh,
      windowsComparison, provenancePkg, pPkg, terminalPkg, refinementPkg, comparisonPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
