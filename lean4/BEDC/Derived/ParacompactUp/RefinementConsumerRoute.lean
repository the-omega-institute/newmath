import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.ParacompactUp.TasteGate

namespace BEDC.Derived.ParacompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ParacompactCarrier_refinement_consumer_route [AskSetup] [PackageSetup]
    {topology cover refinement coverage normal metric transport replay provenance localName
      separationRead metricRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory topology ->
      UnaryHistory cover ->
        UnaryHistory refinement ->
          UnaryHistory coverage ->
            UnaryHistory normal ->
              UnaryHistory metric ->
                UnaryHistory transport ->
                  UnaryHistory replay ->
                    UnaryHistory provenance ->
                      UnaryHistory localName ->
                        Cont topology cover refinement ->
                          Cont refinement coverage normal ->
                            Cont normal metric separationRead ->
                              Cont metric transport metricRead ->
                                Cont separationRead metricRead consumerRead ->
                                  PkgSig bundle provenance pkg ->
                                    PkgSig bundle consumerRead pkg ->
                                      UnaryHistory separationRead ∧ UnaryHistory metricRead ∧
                                        UnaryHistory consumerRead ∧
                                          Cont normal metric separationRead ∧
                                            Cont metric transport metricRead ∧
                                              Cont separationRead metricRead consumerRead ∧
                                                PkgSig bundle provenance pkg ∧
                                                  PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro _topologyUnary _coverUnary _refinementUnary _coverageUnary normalUnary metricUnary
    transportUnary _replayUnary _provenanceUnary _localNameUnary _topologyCoverRefinement
    _refinementCoverageNormal normalMetricSeparation metricTransportRead consumerRoute
    provenancePkg consumerPkg
  have separationUnary : UnaryHistory separationRead :=
    unary_cont_closed normalUnary metricUnary normalMetricSeparation
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed metricUnary transportUnary metricTransportRead
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed separationUnary metricReadUnary consumerRoute
  exact
    ⟨separationUnary, metricReadUnary, consumerReadUnary, normalMetricSeparation,
      metricTransportRead, consumerRoute, provenancePkg, consumerPkg⟩

end BEDC.Derived.ParacompactUp
