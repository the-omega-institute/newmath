import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_fuel_route [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead fuelRead obstructionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont candidateRead finishedRead fuelRead ->
            Cont fuelRead obstruction obstructionRead ->
              Cont obstructionRead replay publicRead ->
                PkgSig bundle publicRead pkg ->
                  UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                    UnaryHistory fuelRead ∧ UnaryHistory obstructionRead ∧
                      UnaryHistory publicRead ∧ Cont candidateRead finishedRead fuelRead ∧
                        Cont fuelRead obstruction obstructionRead ∧
                          Cont obstructionRead replay publicRead ∧
                            hsame transport (append candidate finished) ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead candidateFinishedFuel
    fuelObstructionRead obstructionReplayPublic publicPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have fuelReadUnary : UnaryHistory fuelRead :=
    unary_cont_closed candidateReadUnary finishedReadUnary candidateFinishedFuel
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed fuelReadUnary obstructionUnary fuelObstructionRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed obstructionReadUnary replayUnary obstructionReplayPublic
  exact
    ⟨candidateReadUnary, finishedReadUnary, fuelReadUnary, obstructionReadUnary,
      publicReadUnary, candidateFinishedFuel, fuelObstructionRead, obstructionReplayPublic,
      transportSameCandidateFinished, provenancePkg, publicPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
