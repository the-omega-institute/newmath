import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyInterleavingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyInterleavingPacket [AskSetup] [PackageSetup]
    (leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftName ∧ UnaryHistory rightName ∧ UnaryHistory leftSchedule ∧
    UnaryHistory rightSchedule ∧ UnaryHistory selector ∧ UnaryHistory modulus ∧
      UnaryHistory transport ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ Cont selector leftSchedule leftSeal ∧
        Cont selector rightSchedule rightSeal ∧ Cont leftSeal rightSeal interleavedSeal ∧
          Cont interleavedSeal modulus endpoint ∧ PkgSig bundle endpoint pkg

theorem RegularCauchyInterleavingPacket_classifier_transport [AskSetup] [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint leftName' rightName'
      leftSeal' rightSeal' interleavedSeal' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
        modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert endpoint
        bundle pkg ->
      hsame leftName leftName' ->
        hsame rightName rightName' ->
          Cont selector leftSchedule leftSeal' ->
            Cont selector rightSchedule rightSeal' ->
              Cont leftSeal' rightSeal' interleavedSeal' ->
                Cont interleavedSeal' modulus endpoint' ->
                  PkgSig bundle endpoint' pkg ->
                    RegularCauchyInterleavingPacket leftName' rightName' leftSchedule
                        rightSchedule selector modulus leftSeal' rightSeal' interleavedSeal'
                        transport routes provenance nameCert endpoint' bundle pkg ∧
                      hsame leftSeal leftSeal' ∧ hsame rightSeal rightSeal' ∧
                        hsame interleavedSeal interleavedSeal' ∧ hsame endpoint endpoint' := by
  intro packet sameLeftName sameRightName leftSealRoute rightSealRoute interleavedRoute
    endpointRoute endpointPkg
  obtain ⟨leftNameUnary, rightNameUnary, leftScheduleUnary, rightScheduleUnary, selectorUnary,
    modulusUnary, transportUnary, routesUnary, provenanceUnary, nameCertUnary, leftSealOld,
    rightSealOld, interleavedOld, endpointOld, _endpointPkg⟩ := packet
  have leftNameUnary' : UnaryHistory leftName' :=
    unary_transport leftNameUnary sameLeftName
  have rightNameUnary' : UnaryHistory rightName' :=
    unary_transport rightNameUnary sameRightName
  have leftSealUnary' : UnaryHistory leftSeal' :=
    unary_cont_closed selectorUnary leftScheduleUnary leftSealRoute
  have rightSealUnary' : UnaryHistory rightSeal' :=
    unary_cont_closed selectorUnary rightScheduleUnary rightSealRoute
  have interleavedUnary' : UnaryHistory interleavedSeal' :=
    unary_cont_closed leftSealUnary' rightSealUnary' interleavedRoute
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed interleavedUnary' modulusUnary endpointRoute
  have sameLeftSeal : hsame leftSeal leftSeal' :=
    cont_respects_hsame (hsame_refl selector) (hsame_refl leftSchedule) leftSealOld
      leftSealRoute
  have sameRightSeal : hsame rightSeal rightSeal' :=
    cont_respects_hsame (hsame_refl selector) (hsame_refl rightSchedule) rightSealOld
      rightSealRoute
  have sameInterleaved : hsame interleavedSeal interleavedSeal' :=
    cont_respects_hsame sameLeftSeal sameRightSeal interleavedOld interleavedRoute
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameInterleaved (hsame_refl modulus) endpointOld endpointRoute
  exact
    ⟨⟨leftNameUnary', rightNameUnary', leftScheduleUnary, rightScheduleUnary, selectorUnary,
        modulusUnary, transportUnary, routesUnary, provenanceUnary, nameCertUnary, leftSealRoute,
        rightSealRoute, interleavedRoute, endpointRoute, endpointPkg⟩,
      sameLeftSeal, sameRightSeal, sameInterleaved, sameEndpoint⟩

end BEDC.Derived.RegularCauchyInterleavingUp
