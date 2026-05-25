import BEDC.Derived.SeparatedMetricUp.TasteGate

namespace BEDC.Derived.SeparatedMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparatedMetricPacket_real_completion_consumer_boundary [AskSetup] [PackageSetup]
    {metric apartness zeroDistance limitWitness completionRoute transport provenance nameCert
      endpoint completionRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparatedMetricPacket metric apartness zeroDistance limitWitness completionRoute transport
        provenance nameCert endpoint bundle pkg ->
      Cont limitWitness completionRoute completionRead ->
        Cont completionRead zeroDistance realRead ->
          PkgSig bundle realRead pkg ->
            UnaryHistory metric ∧ UnaryHistory zeroDistance ∧ UnaryHistory limitWitness ∧
              UnaryHistory completionRoute ∧ UnaryHistory completionRead ∧
                UnaryHistory realRead ∧ Cont limitWitness completionRoute completionRead ∧
                  Cont completionRead zeroDistance realRead ∧ PkgSig bundle nameCert pkg ∧
                    PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet completionRouteRead realRoute realPkg
  obtain ⟨metricUnary, _apartnessUnary, zeroUnary, limitUnary, completionUnary,
    _transportUnary, _provenanceUnary, _nameCertUnary, _endpointUnary, _limitRoute,
    _transportRoute, _endpointRoute, nameCertPkg⟩ := packet
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed limitUnary completionUnary completionRouteRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed completionReadUnary zeroUnary realRoute
  exact
    ⟨metricUnary, zeroUnary, limitUnary, completionUnary, completionReadUnary,
      realReadUnary, completionRouteRead, realRoute, nameCertPkg, realPkg⟩

end BEDC.Derived.SeparatedMetricUp
