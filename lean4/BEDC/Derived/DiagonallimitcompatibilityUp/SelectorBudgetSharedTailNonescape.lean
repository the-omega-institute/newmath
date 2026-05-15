import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_selector_budget_shared_tail_nonescape
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      synchronizer tail selector endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont dyadic windows synchronizer →
        Cont synchronizer readback tail →
          Cont tail realSeal selector →
            Cont selector cert endpoint →
              PkgSig bundle endpoint pkg →
                UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                  UnaryHistory realSeal ∧ UnaryHistory cert ∧ UnaryHistory synchronizer ∧
                    UnaryHistory tail ∧ UnaryHistory selector ∧ UnaryHistory endpoint ∧
                      Cont dyadic windows synchronizer ∧ Cont synchronizer readback tail ∧
                        Cont tail realSeal selector ∧ Cont selector cert endpoint ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier dyadicWindowsSynchronizer synchronizerReadbackTail tailRealSealSelector
    selectorCertEndpoint endpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have synchronizerUnary : UnaryHistory synchronizer :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsSynchronizer
  have tailUnary : UnaryHistory tail :=
    unary_cont_closed synchronizerUnary readbackUnary synchronizerReadbackTail
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed tailUnary realSealUnary tailRealSealSelector
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed selectorUnary certUnary selectorCertEndpoint
  exact
    ⟨dyadicUnary, windowsUnary, readbackUnary, realSealUnary, certUnary, synchronizerUnary,
      tailUnary, selectorUnary, endpointUnary, dyadicWindowsSynchronizer,
      synchronizerReadbackTail, tailRealSealSelector, selectorCertEndpoint, provenancePkg,
      endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
