import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityTerminalSynchronizerClassifier [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      synchronizer terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont sealRow realSeal synchronizer →
        Cont synchronizer cert terminal →
          PkgSig bundle terminal pkg →
            UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
              UnaryHistory realSeal ∧ UnaryHistory synchronizer ∧ UnaryHistory terminal ∧
                Cont diagonal triangle sealRow ∧ Cont sealRow realSeal synchronizer ∧
                  Cont synchronizer cert terminal ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle
  intro carrier sealRealSynchronizer synchronizerCertTerminal terminalPkg
  obtain ⟨diagonalUnary, triangleUnary, sealUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have synchronizerUnary : UnaryHistory synchronizer :=
    unary_cont_closed sealUnary realSealUnary sealRealSynchronizer
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed synchronizerUnary certUnary synchronizerCertTerminal
  exact
    ⟨diagonalUnary, triangleUnary, sealUnary, realSealUnary, synchronizerUnary,
      terminalUnary, diagonalTriangleSeal, sealRealSynchronizer, synchronizerCertTerminal,
      provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
