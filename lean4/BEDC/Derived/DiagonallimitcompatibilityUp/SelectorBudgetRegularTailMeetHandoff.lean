import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.Derived.RegularCauchyTailMeetUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RegularCauchyTailMeetUp

theorem DiagonalLimitCompatibilityCarrier_selector_budget_regular_tail_meet_handoff
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      r0 r1 w0 w1 m0 m1 tau q h c l n threshold terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau q h c l n bundle pkg →
        Cont dyadic windows threshold →
          Cont threshold tau terminal →
            PkgSig bundle terminal pkg →
              UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory tau ∧
                UnaryHistory threshold ∧ UnaryHistory terminal ∧
                  Cont dyadic windows threshold ∧ Cont threshold tau terminal ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle l pkg ∧
                      PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier packet dyadicWindowsThreshold thresholdTauTerminal terminalPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  obtain ⟨_r0Unary, _r1Unary, _w0Unary, _w1Unary, _m0Unary, _m1Unary, tauUnary,
    _qUnary, _hUnary, _cUnary, _lUnary, _nUnary, _r0w0Row, _r1w1Row, _m0m1Row,
    _tauqRow, lPkg⟩ := packet
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsThreshold
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed thresholdUnary tauUnary thresholdTauTerminal
  exact
    ⟨dyadicUnary, windowsUnary, tauUnary, thresholdUnary, terminalUnary,
      dyadicWindowsThreshold, thresholdTauTerminal, provenancePkg, lPkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
