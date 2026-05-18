import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_fuel_ledger_nonescape [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead obstructionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont candidateRead obstruction obstructionRead ->
            Cont obstructionRead replay publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                  UnaryHistory obstructionRead ∧ UnaryHistory publicRead ∧
                    Cont candidate closedCandidate candidateRead ∧
                      Cont finished endpoint finishedRead ∧
                        Cont candidateRead obstruction obstructionRead ∧
                          Cont obstructionRead replay publicRead ∧
                            hsame transport (append candidate finished) ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead candidateObstructionRead
    obstructionReplayPublic publicPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed candidateReadUnary obstructionUnary candidateObstructionRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed obstructionReadUnary replayUnary obstructionReplayPublic
  exact
    ⟨candidateReadUnary, finishedReadUnary, obstructionReadUnary, publicReadUnary,
      candidateClosedRead, finishedEndpointRead, candidateObstructionRead,
      obstructionReplayPublic, transportSameCandidateFinished, provenancePkg, publicPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
