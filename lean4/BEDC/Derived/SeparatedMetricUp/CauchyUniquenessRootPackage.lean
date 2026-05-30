import BEDC.Derived.SeparatedMetricUp.CompletionLimitUniquenessRoute

namespace BEDC.Derived.SeparatedMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparatedMetricPacket_cauchy_uniqueness_root_package [AskSetup] [PackageSetup]
    {metric apartness zeroDistance limitWitness completionRoute transport provenance nameCert
      endpoint limitRead zeroRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparatedMetricPacket metric apartness zeroDistance limitWitness completionRoute transport
        provenance nameCert endpoint bundle pkg →
      Cont limitWitness completionRoute limitRead →
        Cont limitRead zeroDistance zeroRead →
          Cont zeroRead apartness classifierRead →
            PkgSig bundle classifierRead pkg →
              UnaryHistory metric ∧ UnaryHistory apartness ∧ UnaryHistory zeroDistance ∧
                UnaryHistory limitWitness ∧ UnaryHistory completionRoute ∧
                  UnaryHistory limitRead ∧ UnaryHistory zeroRead ∧
                    UnaryHistory classifierRead ∧
                      Cont limitWitness completionRoute limitRead ∧
                        Cont limitRead zeroDistance zeroRead ∧
                          Cont zeroRead apartness classifierRead ∧
                            PkgSig bundle nameCert pkg ∧ PkgSig bundle classifierRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet limitRoute zeroRoute classifierRoute classifierPkg
  have route :=
    SeparatedMetricPacket_completion_limit_uniqueness_route
      (metric := metric) (apartness := apartness) (zeroDistance := zeroDistance)
      (limitWitness := limitWitness) (completionRoute := completionRoute)
      (transport := transport) (provenance := provenance) (nameCert := nameCert)
      (endpoint := endpoint) (limitRead := limitRead) (zeroRead := zeroRead)
      (classifierRead := classifierRead) (bundle := bundle) (pkg := pkg)
      packet limitRoute zeroRoute classifierRoute
  obtain ⟨metricUnary, apartnessUnary, zeroUnary, limitWitnessUnary, completionUnary,
    limitReadUnary, zeroReadUnary, classifierReadUnary, limitRouteOut, zeroRouteOut,
    classifierRouteOut, nameCertPkg⟩ := route
  exact
    ⟨metricUnary, apartnessUnary, zeroUnary, limitWitnessUnary, completionUnary,
      limitReadUnary, zeroReadUnary, classifierReadUnary, limitRouteOut, zeroRouteOut,
      classifierRouteOut, nameCertPkg, classifierPkg⟩

end BEDC.Derived.SeparatedMetricUp
