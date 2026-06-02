import BEDC.Derived.RegularCauchyInterleavingUp

namespace BEDC.Derived.RegularCauchyInterleavingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyInterleavingPacket_finite_tail_budget_route [AskSetup] [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint tailRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
        modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert endpoint
        bundle pkg →
      Cont endpoint nameCert tailRead →
        Cont tailRead provenance publicRead →
          PkgSig bundle publicRead pkg →
            UnaryHistory endpoint ∧ UnaryHistory tailRead ∧ UnaryHistory publicRead ∧
              Cont endpoint nameCert tailRead ∧ Cont tailRead provenance publicRead ∧
                PkgSig bundle endpoint pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro packet endpointNameTail tailProvenancePublic publicPkg
  obtain ⟨_leftNameUnary, _rightNameUnary, leftScheduleUnary, rightScheduleUnary,
    selectorUnary, modulusUnary, _transportUnary, _routesUnary, provenanceUnary,
    nameCertUnary, leftSealRoute, rightSealRoute, interleavedRoute, endpointRoute,
    endpointPkg⟩ := packet
  have leftSealUnary : UnaryHistory leftSeal :=
    unary_cont_closed selectorUnary leftScheduleUnary leftSealRoute
  have rightSealUnary : UnaryHistory rightSeal :=
    unary_cont_closed selectorUnary rightScheduleUnary rightSealRoute
  have interleavedUnary : UnaryHistory interleavedSeal :=
    unary_cont_closed leftSealUnary rightSealUnary interleavedRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed interleavedUnary modulusUnary endpointRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed endpointUnary nameCertUnary endpointNameTail
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed tailUnary provenanceUnary tailProvenancePublic
  exact
    ⟨endpointUnary, tailUnary, publicUnary, endpointNameTail, tailProvenancePublic,
      endpointPkg, publicPkg⟩

end BEDC.Derived.RegularCauchyInterleavingUp
