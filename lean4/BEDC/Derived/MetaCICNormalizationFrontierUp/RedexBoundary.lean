import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_redex_boundary [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead endpointRead obstructionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg →
      Cont candidate closedCandidate candidateRead →
        Cont finished endpoint finishedRead →
          Cont endpoint replay endpointRead →
            Cont obstruction transport obstructionRead →
              Cont endpointRead obstructionRead publicRead →
                PkgSig bundle publicRead pkg →
                  UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                    UnaryHistory endpointRead ∧ UnaryHistory obstructionRead ∧
                      UnaryHistory publicRead ∧
                        Cont candidate closedCandidate candidateRead ∧
                          Cont finished endpoint finishedRead ∧
                            Cont endpoint replay endpointRead ∧
                              Cont obstruction transport obstructionRead ∧
                                Cont endpointRead obstructionRead publicRead ∧
                                  hsame transport (append candidate finished) ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead endpointReplayRead
    obstructionTransportRead endpointObstructionPublic publicPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary transportUnary obstructionTransportRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointReadUnary obstructionReadUnary endpointObstructionPublic
  exact
    ⟨candidateReadUnary, finishedReadUnary, endpointReadUnary, obstructionReadUnary,
      publicReadUnary, candidateClosedRead, finishedEndpointRead, endpointReplayRead,
      obstructionTransportRead, endpointObstructionPublic, transportSameCandidateFinished,
      provenancePkg, publicPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
