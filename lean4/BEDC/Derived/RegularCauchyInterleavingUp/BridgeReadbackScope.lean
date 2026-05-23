import BEDC.Derived.RegularCauchyInterleavingUp

namespace BEDC.Derived.RegularCauchyInterleavingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyInterleavingPacket_bridge_readback_scope [AskSetup] [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint publicRead bridgeRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
        modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert endpoint
        bundle pkg →
      Cont endpoint provenance publicRead →
        Cont publicRead routes bridgeRead →
          PkgSig bundle bridgeRead pkg →
            UnaryHistory bridgeRead ∧ UnaryHistory leftSchedule ∧
              UnaryHistory rightSchedule ∧ UnaryHistory interleavedSeal ∧
                Cont endpoint provenance publicRead ∧ Cont publicRead routes bridgeRead ∧
                  PkgSig bundle endpoint pkg ∧ PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro packet publicRoute bridgeRoute bridgePkg
  obtain ⟨_leftNameUnary, _rightNameUnary, leftScheduleUnary, rightScheduleUnary,
    selectorUnary, modulusUnary, _transportUnary, routesUnary, provenanceUnary,
    _nameCertUnary, leftSealRoute, rightSealRoute, interleavedRoute, endpointRoute,
    endpointPkg⟩ := packet
  have leftSealUnary : UnaryHistory leftSeal :=
    unary_cont_closed selectorUnary leftScheduleUnary leftSealRoute
  have rightSealUnary : UnaryHistory rightSeal :=
    unary_cont_closed selectorUnary rightScheduleUnary rightSealRoute
  have interleavedUnary : UnaryHistory interleavedSeal :=
    unary_cont_closed leftSealUnary rightSealUnary interleavedRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed interleavedUnary modulusUnary endpointRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointUnary provenanceUnary publicRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed publicUnary routesUnary bridgeRoute
  exact
    ⟨bridgeUnary, leftScheduleUnary, rightScheduleUnary, interleavedUnary, publicRoute,
      bridgeRoute, endpointPkg, bridgePkg⟩

end BEDC.Derived.RegularCauchyInterleavingUp
