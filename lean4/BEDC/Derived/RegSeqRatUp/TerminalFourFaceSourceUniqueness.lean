import BEDC.Derived.RegSeqRatUp.RealTerminalFourFaceExactness

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegSeqRatTerminalFourFaceSourceUniqueness [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback streamFace dyadicFace
      realFace terminal0 terminal1 : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
        bundle pkg ->
      Cont schedule index streamFace ->
        Cont endpoint radius dyadicFace ->
          Cont regularity provenance realFace ->
            Cont streamFace realFace terminal0 ->
              Cont streamFace realFace terminal1 ->
                PkgSig bundle terminal0 pkg ->
                  PkgSig bundle terminal1 pkg ->
                    hsame terminal0 terminal1 ∧ UnaryHistory streamFace ∧
                      UnaryHistory dyadicFace ∧ UnaryHistory realFace := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier streamRoute dyadicRoute realRoute terminalRoute0 terminalRoute1 _terminalPkg0
    _terminalPkg1
  obtain ⟨scheduleUnary, indexUnary, endpointUnary, radiusUnary, regularityUnary,
    provenanceUnary, _readbackUnary, _carrierStreamRoute, _carrierDyadicRoute,
    _carrierRealRoute, _readbackPkg⟩ := carrier
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed scheduleUnary indexUnary streamRoute
  have dyadicUnary : UnaryHistory dyadicFace :=
    unary_cont_closed endpointUnary radiusUnary dyadicRoute
  have realUnary : UnaryHistory realFace :=
    unary_cont_closed regularityUnary provenanceUnary realRoute
  have terminalSame : hsame terminal0 terminal1 :=
    cont_deterministic terminalRoute0 terminalRoute1
  exact ⟨terminalSame, streamUnary, dyadicUnary, realUnary⟩

end BEDC.Derived.RegSeqRatUp
