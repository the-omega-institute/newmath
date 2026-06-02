import BEDC.Derived.RegularCauchyInterleavingUp

namespace BEDC.Derived.RegularCauchyInterleavingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyInterleavingPacket_regseqrat_real_consumer_factorization [AskSetup]
    [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
        modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert endpoint
        bundle pkg ->
      Cont interleavedSeal modulus endpointRead ->
        PkgSig bundle endpointRead pkg ->
          UnaryHistory leftName ∧ UnaryHistory rightName ∧ UnaryHistory leftSchedule ∧
            UnaryHistory rightSchedule ∧ UnaryHistory endpointRead ∧
              hsame endpoint endpointRead ∧ PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro packet endpointReadRoute endpointReadPkg
  obtain ⟨leftNameUnary, rightNameUnary, leftScheduleUnary, rightScheduleUnary, _selectorUnary,
    modulusUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary,
    _leftSealRoute, _rightSealRoute, interleavedRoute, endpointRoute, _endpointPkg⟩ := packet
  have leftSealUnary : UnaryHistory leftSeal :=
    unary_cont_closed _selectorUnary leftScheduleUnary _leftSealRoute
  have rightSealUnary : UnaryHistory rightSeal :=
    unary_cont_closed _selectorUnary rightScheduleUnary _rightSealRoute
  have interleavedUnary : UnaryHistory interleavedSeal :=
    unary_cont_closed leftSealUnary rightSealUnary interleavedRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed interleavedUnary modulusUnary endpointReadRoute
  have sameEndpoint : hsame endpoint endpointRead :=
    cont_respects_hsame (hsame_refl interleavedSeal) (hsame_refl modulus) endpointRoute
      endpointReadRoute
  exact
    ⟨leftNameUnary, rightNameUnary, leftScheduleUnary, rightScheduleUnary, endpointReadUnary,
      sameEndpoint, endpointReadPkg⟩

end BEDC.Derived.RegularCauchyInterleavingUp
