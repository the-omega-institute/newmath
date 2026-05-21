import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberL10PhaseConsumerReadiness [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow rootRead phaseRead
      consumerRead terminalRead compactRead compactNetRead continuousRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow rootRead ->
        Cont rootRead radius phaseRead ->
          Cont phaseRead mesh consumerRead ->
            Cont route nameRow terminalRead ->
              Cont terminalRead radius compactRead ->
                Cont compactRead mesh compactNetRead ->
                  Cont compactNetRead route continuousRead ->
                    Cont continuousRead nameRow uniformRead ->
                      PkgSig bundle uniformRead pkg ->
                        UnaryHistory rootRead ∧ UnaryHistory phaseRead ∧
                          UnaryHistory consumerRead ∧ UnaryHistory terminalRead ∧
                            UnaryHistory compactRead ∧ UnaryHistory compactNetRead ∧
                              UnaryHistory continuousRead ∧ UnaryHistory uniformRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier routeNameRoot rootRadiusPhase phaseMeshConsumer routeNameTerminal
    terminalRadiusCompact compactMeshNet netRouteContinuous continuousNameUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameRoot
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed rootUnary radiusUnary rootRadiusPhase
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed phaseUnary meshUnary phaseMeshConsumer
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameTerminal
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed terminalUnary radiusUnary terminalRadiusCompact
  have compactNetUnary : UnaryHistory compactNetRead :=
    unary_cont_closed compactUnary meshUnary compactMeshNet
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactNetUnary routeUnary netRouteContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  exact
    ⟨rootUnary, phaseUnary, consumerUnary, terminalUnary, compactUnary, compactNetUnary,
      continuousUnary, uniformUnary, provenancePkg, uniformPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
