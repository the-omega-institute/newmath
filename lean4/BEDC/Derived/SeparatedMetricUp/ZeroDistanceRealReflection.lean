import BEDC.Derived.SeparatedMetricUp.TasteGate

namespace BEDC.Derived.SeparatedMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparatedMetricPacket_zero_distance_real_reflection [AskSetup] [PackageSetup]
    {metric apartness zeroDistance limitWitness completionRoute transport provenance nameCert
      endpoint zeroRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparatedMetricPacket metric apartness zeroDistance limitWitness completionRoute transport
        provenance nameCert endpoint bundle pkg ->
      hsame zeroRead zeroDistance ->
        Cont limitWitness completionRoute completionRead ->
          PkgSig bundle completionRead pkg ->
            UnaryHistory metric ∧ UnaryHistory zeroRead ∧ UnaryHistory apartness ∧
              UnaryHistory limitWitness ∧ UnaryHistory completionRead ∧
                Cont apartness zeroDistance limitWitness ∧
                  Cont limitWitness completionRoute completionRead ∧
                    Cont transport provenance endpoint ∧ PkgSig bundle nameCert pkg ∧
                      PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro packet sameZeroRead completionRouteRead completionReadPkg
  obtain ⟨metricUnary, apartnessUnary, zeroDistanceUnary, limitWitnessUnary,
    completionRouteUnary, _transportUnary, _provenanceUnary, _nameCertUnary,
    _endpointUnary, apartnessZeroLimit, _limitRouteTransport, transportProvenanceEndpoint,
    nameCertPkg⟩ := packet
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_transport zeroDistanceUnary (hsame_symm sameZeroRead)
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed limitWitnessUnary completionRouteUnary completionRouteRead
  exact
    ⟨metricUnary, zeroReadUnary, apartnessUnary, limitWitnessUnary, completionReadUnary,
      apartnessZeroLimit, completionRouteRead, transportProvenanceEndpoint, nameCertPkg,
      completionReadPkg⟩

end BEDC.Derived.SeparatedMetricUp
