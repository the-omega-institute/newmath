import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_obstruction_retention [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead finishedRead obstructionRead retainedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint finishedRead ->
          Cont obstruction transport obstructionRead ->
            Cont obstructionRead replay retainedRead ->
              PkgSig bundle retainedRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row obstruction ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row obstruction ∧ UnaryHistory row ∧
                        Cont obstruction transport obstructionRead ∧
                          Cont obstructionRead replay retainedRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle retainedRead pkg ∧
                        hsame row obstruction)
                    hsame ∧
                  UnaryHistory obstructionRead ∧ UnaryHistory retainedRead ∧
                    Cont obstruction transport obstructionRead ∧
                      Cont obstructionRead replay retainedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier _candidateClosedRead _finishedEndpointRead obstructionTransportRead
    obstructionReplayRetained retainedPkg
  obtain ⟨_candidateUnary, _closedCandidateUnary, _finishedUnary, _endpointUnary,
    obstructionUnary, transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary transportUnary obstructionTransportRead
  have retainedReadUnary : UnaryHistory retainedRead :=
    unary_cont_closed obstructionReadUnary replayUnary obstructionReplayRetained
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obstruction ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row obstruction ∧ UnaryHistory row ∧
              Cont obstruction transport obstructionRead ∧
                Cont obstructionRead replay retainedRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle retainedRead pkg ∧
              hsame row obstruction)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro obstruction ⟨hsame_refl obstruction, obstructionUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨source.left, source.right, obstructionTransportRead,
          obstructionReplayRetained⟩
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, retainedPkg, source.left⟩
  }
  exact
    ⟨cert, obstructionReadUnary, retainedReadUnary, obstructionTransportRead,
      obstructionReplayRetained⟩

theorem MetaCICNormalizationFrontierCarrier_root_obstruction_retention [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance localRow
      candidateRead endpointRead obstructionRead retainedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint endpointRead ->
          Cont obstruction transport obstructionRead ->
            Cont obstructionRead replay retainedRead ->
              PkgSig bundle retainedRead pkg ->
                UnaryHistory obstruction /\ UnaryHistory candidateRead /\
                  UnaryHistory endpointRead /\ UnaryHistory obstructionRead /\
                    UnaryHistory retainedRead /\ hsame obstruction obstruction /\
                      Cont obstruction transport obstructionRead /\
                        Cont obstructionRead replay retainedRead /\
                          PkgSig bundle provenance pkg /\ PkgSig bundle retainedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead obstructionTransportRead
    obstructionReplayRetained retainedPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary transportUnary obstructionTransportRead
  have retainedReadUnary : UnaryHistory retainedRead :=
    unary_cont_closed obstructionReadUnary replayUnary obstructionReplayRetained
  exact
    ⟨obstructionUnary, candidateReadUnary, endpointReadUnary, obstructionReadUnary,
      retainedReadUnary, hsame_refl obstruction, obstructionTransportRead,
      obstructionReplayRetained, provenancePkg, retainedPkg⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
