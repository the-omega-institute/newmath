import BEDC.Derived.SeparatedMetricUp.TasteGate

namespace BEDC.Derived.SeparatedMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparatedMetricPacket_limit_uniqueness_scope [AskSetup] [PackageSetup]
    {metric apartness zeroDistance limitWitness completionRoute transport provenance nameCert
      endpoint limitRead zeroRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparatedMetricPacket metric apartness zeroDistance limitWitness completionRoute transport
        provenance nameCert endpoint bundle pkg ->
      Cont limitWitness completionRoute limitRead ->
        Cont limitRead zeroDistance zeroRead ->
          Cont zeroRead apartness classifierRead ->
            UnaryHistory limitWitness ∧ UnaryHistory completionRoute ∧
              UnaryHistory limitRead ∧ UnaryHistory zeroRead ∧ UnaryHistory classifierRead ∧
                Cont limitWitness completionRoute limitRead ∧
                  Cont limitRead zeroDistance zeroRead ∧
                    Cont zeroRead apartness classifierRead ∧ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet limitRoute zeroRoute classifierRoute
  obtain ⟨_metricUnary, apartnessUnary, zeroUnary, limitWitnessUnary, completionUnary,
    _transportUnary, _provenanceUnary, _nameCertUnary, _endpointUnary, _limitWitnessRoute,
    _transportRoute, _endpointRoute, packageRead⟩ := packet
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed limitWitnessUnary completionUnary limitRoute
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed limitReadUnary zeroUnary zeroRoute
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed zeroReadUnary apartnessUnary classifierRoute
  exact
    ⟨limitWitnessUnary, completionUnary, limitReadUnary, zeroReadUnary, classifierReadUnary,
      limitRoute, zeroRoute, classifierRoute, packageRead⟩

end BEDC.Derived.SeparatedMetricUp
