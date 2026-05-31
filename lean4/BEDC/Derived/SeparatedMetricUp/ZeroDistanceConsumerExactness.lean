import BEDC.Derived.SeparatedMetricUp.TasteGate

namespace BEDC.Derived.SeparatedMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparatedMetricZeroDistanceConsumerExactness [AskSetup] [PackageSetup]
    {metric apartness zeroDistance limitWitness completionRoute transport provenance nameCert
      endpoint zeroRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparatedMetricPacket metric apartness zeroDistance limitWitness completionRoute transport
        provenance nameCert endpoint bundle pkg →
      Cont endpoint zeroDistance zeroRead →
        Cont zeroRead apartness classifierRead →
          PkgSig bundle classifierRead pkg →
            UnaryHistory metric ∧ UnaryHistory zeroDistance ∧ UnaryHistory endpoint ∧
              UnaryHistory zeroRead ∧ UnaryHistory classifierRead ∧
                Cont endpoint zeroDistance zeroRead ∧
                  Cont zeroRead apartness classifierRead ∧ PkgSig bundle nameCert pkg ∧
                    PkgSig bundle classifierRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet zeroRoute classifierRoute classifierPkg
  obtain ⟨metricUnary, apartnessUnary, zeroUnary, _limitWitnessUnary, _completionUnary,
    _transportUnary, _provenanceUnary, _nameCertUnary, endpointUnary, _limitRoute,
    _transportRoute, _endpointRoute, nameCertPkg⟩ := packet
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed endpointUnary zeroUnary zeroRoute
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed zeroReadUnary apartnessUnary classifierRoute
  exact
    ⟨metricUnary, zeroUnary, endpointUnary, zeroReadUnary, classifierReadUnary, zeroRoute,
      classifierRoute, nameCertPkg, classifierPkg⟩

end BEDC.Derived.SeparatedMetricUp
