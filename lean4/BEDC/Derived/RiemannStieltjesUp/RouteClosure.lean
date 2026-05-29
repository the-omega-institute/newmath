import BEDC.Derived.RiemannStieltjesUp.TasteGate

namespace BEDC.Derived.RiemannStieltjesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RiemannStieltjesCarrier_refinement_window_exhaustion [AskSetup] [PackageSetup]
    {regulated variation tagged step handoff sealRow transportRow replayRow provenance nameRow
      meshRead stepRead _handoffRead endpointRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannStieltjesCarrier regulated variation tagged step handoff sealRow transportRow replayRow
      provenance nameRow bundle pkg ->
      Cont tagged step meshRead ->
        Cont meshRead handoff stepRead ->
          Cont stepRead sealRow endpointRead ->
            Cont endpointRead replayRow terminalRead ->
              PkgSig bundle terminalRead pkg ->
                UnaryHistory tagged ∧ UnaryHistory step ∧ UnaryHistory handoff ∧
                  UnaryHistory sealRow ∧ UnaryHistory replayRow ∧ UnaryHistory meshRead ∧
                    UnaryHistory stepRead ∧ UnaryHistory endpointRead ∧
                      UnaryHistory terminalRead ∧ Cont tagged step meshRead ∧
                        Cont meshRead handoff stepRead ∧
                          Cont stepRead sealRow endpointRead ∧
                            Cont endpointRead replayRow terminalRead ∧
                              PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier meshRoute stepRoute endpointRoute terminalRoute terminalPkg
  obtain ⟨_regulatedUnary, _variationUnary, taggedUnary, stepUnary, handoffUnary,
    sealUnary, _transportUnary, replayUnary, _provenanceUnary, _regulatedTaggedRoute,
    _taggedStepRoute, _handoffSealRoute, _namePkg⟩ := carrier
  have meshUnary : UnaryHistory meshRead :=
    unary_cont_closed taggedUnary stepUnary meshRoute
  have stepReadUnary : UnaryHistory stepRead :=
    unary_cont_closed meshUnary handoffUnary stepRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed stepReadUnary sealUnary endpointRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed endpointReadUnary replayUnary terminalRoute
  exact
    ⟨taggedUnary, stepUnary, handoffUnary, sealUnary, replayUnary, meshUnary,
      stepReadUnary, endpointReadUnary, terminalReadUnary, meshRoute, stepRoute,
      endpointRoute, terminalRoute, terminalPkg⟩

theorem RiemannStieltjesCarrier_regulated_integrator_transport [AskSetup] [PackageSetup]
    {regulated variation tagged step handoff sealRow transportRow replayRow provenance nameRow
      integratorRead taggedRead stepRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannStieltjesCarrier regulated variation tagged step handoff sealRow transportRow replayRow
      provenance nameRow bundle pkg ->
      Cont variation tagged integratorRead ->
        Cont integratorRead step taggedRead ->
          Cont taggedRead handoff stepRead ->
            Cont stepRead sealRow handoffRead ->
              PkgSig bundle handoffRead pkg ->
                UnaryHistory variation ∧ UnaryHistory tagged ∧ UnaryHistory step ∧
                  UnaryHistory handoff ∧ UnaryHistory sealRow ∧ UnaryHistory integratorRead ∧
                    UnaryHistory taggedRead ∧ UnaryHistory stepRead ∧
                      UnaryHistory handoffRead ∧ Cont variation tagged integratorRead ∧
                        Cont integratorRead step taggedRead ∧
                          Cont taggedRead handoff stepRead ∧
                            Cont stepRead sealRow handoffRead ∧
                              PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier integratorRoute taggedRoute stepRoute handoffRoute handoffPkg
  obtain ⟨_regulatedUnary, variationUnary, taggedUnary, stepUnary, handoffUnary,
    sealUnary, _transportUnary, _replayUnary, _provenanceUnary, _regulatedTaggedRoute,
    _taggedStepRoute, _handoffSealRoute, _namePkg⟩ := carrier
  have integratorReadUnary : UnaryHistory integratorRead :=
    unary_cont_closed variationUnary taggedUnary integratorRoute
  have taggedReadUnary : UnaryHistory taggedRead :=
    unary_cont_closed integratorReadUnary stepUnary taggedRoute
  have stepReadUnary : UnaryHistory stepRead :=
    unary_cont_closed taggedReadUnary handoffUnary stepRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed stepReadUnary sealUnary handoffRoute
  exact
    ⟨variationUnary, taggedUnary, stepUnary, handoffUnary, sealUnary, integratorReadUnary,
      taggedReadUnary, stepReadUnary, handoffReadUnary, integratorRoute, taggedRoute,
      stepRoute, handoffRoute, handoffPkg⟩

end BEDC.Derived.RiemannStieltjesUp
