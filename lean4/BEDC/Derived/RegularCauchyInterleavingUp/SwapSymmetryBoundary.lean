import BEDC.Derived.RegularCauchyInterleavingUp

namespace BEDC.Derived.RegularCauchyInterleavingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyInterleavingPacket_swap_symmetry_boundary [AskSetup] [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint swappedRightSeal
      swappedLeftSeal swappedInterleaved swappedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
        modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert endpoint
        bundle pkg ->
      Cont selector rightSchedule swappedRightSeal ->
        Cont selector leftSchedule swappedLeftSeal ->
          Cont swappedRightSeal swappedLeftSeal swappedInterleaved ->
            Cont swappedInterleaved modulus swappedEndpoint ->
              PkgSig bundle swappedEndpoint pkg ->
                UnaryHistory swappedRightSeal ∧ UnaryHistory swappedLeftSeal ∧
                  UnaryHistory swappedInterleaved ∧ UnaryHistory swappedEndpoint ∧
                    hsame rightSeal swappedRightSeal ∧ hsame leftSeal swappedLeftSeal ∧
                      PkgSig bundle endpoint pkg ∧ PkgSig bundle swappedEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig UnaryHistory
  intro packet swappedRightRoute swappedLeftRoute swappedInterleavedRoute
    swappedEndpointRoute swappedEndpointPkg
  obtain ⟨_leftNameUnary, _rightNameUnary, leftScheduleUnary, rightScheduleUnary,
    selectorUnary, modulusUnary, _transportUnary, _routesUnary, _provenanceUnary,
    _nameCertUnary, leftSealRoute, rightSealRoute, _interleavedRoute, _endpointRoute,
    endpointPkg⟩ := packet
  have swappedRightUnary : UnaryHistory swappedRightSeal :=
    unary_cont_closed selectorUnary rightScheduleUnary swappedRightRoute
  have swappedLeftUnary : UnaryHistory swappedLeftSeal :=
    unary_cont_closed selectorUnary leftScheduleUnary swappedLeftRoute
  have swappedInterleavedUnary : UnaryHistory swappedInterleaved :=
    unary_cont_closed swappedRightUnary swappedLeftUnary swappedInterleavedRoute
  have swappedEndpointUnary : UnaryHistory swappedEndpoint :=
    unary_cont_closed swappedInterleavedUnary modulusUnary swappedEndpointRoute
  have sameRightSeal : hsame rightSeal swappedRightSeal :=
    cont_respects_hsame (hsame_refl selector) (hsame_refl rightSchedule) rightSealRoute
      swappedRightRoute
  have sameLeftSeal : hsame leftSeal swappedLeftSeal :=
    cont_respects_hsame (hsame_refl selector) (hsame_refl leftSchedule) leftSealRoute
      swappedLeftRoute
  exact
    ⟨swappedRightUnary, swappedLeftUnary, swappedInterleavedUnary, swappedEndpointUnary,
      sameRightSeal, sameLeftSeal, endpointPkg, swappedEndpointPkg⟩

end BEDC.Derived.RegularCauchyInterleavingUp
