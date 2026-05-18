import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_obstruction_ledger [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead obstructionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg →
      Cont candidate closedCandidate candidateRead →
        Cont finished endpoint finishedRead →
          Cont obstruction transport obstructionRead →
            Cont obstructionRead replay publicRead →
              PkgSig bundle publicRead pkg →
                UnaryHistory obstruction ∧ UnaryHistory obstructionRead ∧
                  UnaryHistory publicRead ∧ Cont obstruction transport obstructionRead ∧
                    Cont obstructionRead replay publicRead ∧
                      hsame transport (append candidate finished) ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier _candidateClosedRead _finishedEndpointRead obstructionTransportRead
    obstructionReplayPublic publicPkg
  obtain ⟨_candidateUnary, _closedCandidateUnary, _finishedUnary, _endpointUnary,
    obstructionUnary, transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary transportUnary obstructionTransportRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed obstructionReadUnary replayUnary obstructionReplayPublic
  exact
    ⟨obstructionUnary, obstructionReadUnary, publicReadUnary, obstructionTransportRead,
      obstructionReplayPublic, transportSameCandidateFinished, provenancePkg, publicPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
