import BEDC.Derived.RegularCauchyTailMeetUp
import BEDC.Derived.DyadicAbsoluteValueUp

namespace BEDC.Derived.RegularCauchyTailMeetUp

open BEDC.Derived.DyadicAbsoluteValueUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailMeetPacket_dyadic_absolute_value_handoff [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 m0 m1 tau q h c l n dyadicEndpoint dyadicTolerance
      dyadicSource dyadicSign dyadicMantissa dyadicTransport dyadicRoutes dyadicProvenance
      dyadicName handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau q h c l n bundle pkg →
      DyadicAbsoluteValuePacket dyadicSource dyadicSign dyadicMantissa dyadicEndpoint
        dyadicTolerance dyadicTransport dyadicRoutes dyadicProvenance dyadicName bundle pkg →
      Cont tau dyadicTolerance dyadicEndpoint →
        Cont dyadicEndpoint q handoffRead →
          PkgSig bundle dyadicEndpoint pkg →
            PkgSig bundle handoffRead pkg →
              UnaryHistory tau ∧ UnaryHistory q ∧ UnaryHistory dyadicEndpoint ∧
                UnaryHistory handoffRead ∧ Cont m0 m1 tau ∧ Cont tau q l ∧
                  Cont tau dyadicTolerance dyadicEndpoint ∧
                    Cont dyadicEndpoint q handoffRead ∧ PkgSig bundle l pkg ∧
                      PkgSig bundle dyadicEndpoint pkg ∧
                        PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet dyadicPacket endpointRoute handoffRoute endpointPkg handoffPkg
  obtain ⟨_r0Unary, _r1Unary, _w0Unary, _w1Unary, _m0Unary, _m1Unary,
    tauUnary, qUnary, _hUnary, _cUnary, _lUnary, _nUnary,
    _r0w0Row, _r1w1Row, m0m1Row, tauqRow, pkgRow⟩ := packet
  obtain ⟨_sourceUnary, _signUnary, _mantissaUnary, endpointUnary, _toleranceUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _dyadicNameUnary,
    _sourceSignMantissa, _signMantissaEndpoint, _endpointToleranceRoutes,
    _routesProvenanceName, _dyadicPkg⟩ := dyadicPacket
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed endpointUnary qUnary handoffRoute
  exact
    ⟨tauUnary, qUnary, endpointUnary, handoffUnary, m0m1Row, tauqRow, endpointRoute,
      handoffRoute, pkgRow, endpointPkg, handoffPkg⟩

end BEDC.Derived.RegularCauchyTailMeetUp
