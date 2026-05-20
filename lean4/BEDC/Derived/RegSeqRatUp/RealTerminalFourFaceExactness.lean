import BEDC.Derived.RegSeqRatUp

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegSeqRatStreamCarrier_real_terminal_four_face_exactness [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback streamFace dyadicFace
      realFace : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
        bundle pkg ->
      Cont schedule index streamFace ->
        Cont endpoint radius dyadicFace ->
          Cont regularity provenance realFace ->
            PkgSig bundle realFace pkg ->
              UnaryHistory schedule ∧ UnaryHistory index ∧ UnaryHistory endpoint ∧
                UnaryHistory radius ∧ UnaryHistory regularity ∧ UnaryHistory provenance ∧
                  UnaryHistory readback ∧ UnaryHistory streamFace ∧
                    UnaryHistory dyadicFace ∧ UnaryHistory realFace ∧
                      hsame endpoint streamFace ∧ hsame regularity dyadicFace ∧
                        hsame readback realFace ∧ Cont schedule index streamFace ∧
                          Cont endpoint radius dyadicFace ∧ Cont regularity provenance realFace ∧
                            PkgSig bundle readback pkg ∧ PkgSig bundle realFace pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier streamRoute dyadicRoute realRoute realPkg
  obtain ⟨scheduleUnary, indexUnary, endpointUnary, radiusUnary, regularityUnary,
    provenanceUnary, readbackUnary, carrierStreamRoute, carrierDyadicRoute, carrierRealRoute,
    readbackPkg⟩ := carrier
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed scheduleUnary indexUnary streamRoute
  have dyadicUnary : UnaryHistory dyadicFace :=
    unary_cont_closed endpointUnary radiusUnary dyadicRoute
  have realUnary : UnaryHistory realFace :=
    unary_cont_closed regularityUnary provenanceUnary realRoute
  have endpointSameStream : hsame endpoint streamFace :=
    cont_deterministic carrierStreamRoute streamRoute
  have regularitySameDyadic : hsame regularity dyadicFace :=
    cont_deterministic carrierDyadicRoute dyadicRoute
  have readbackSameReal : hsame readback realFace :=
    cont_deterministic carrierRealRoute realRoute
  exact
    ⟨scheduleUnary, indexUnary, endpointUnary, radiusUnary, regularityUnary,
      provenanceUnary, readbackUnary, streamUnary, dyadicUnary, realUnary,
      endpointSameStream, regularitySameDyadic, readbackSameReal, streamRoute,
      dyadicRoute, realRoute, readbackPkg, realPkg⟩

end BEDC.Derived.RegSeqRatUp
