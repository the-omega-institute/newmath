import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_consumer_route_public_exhaustion
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead endpointRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg →
      Cont candidate closedCandidate candidateRead →
        Cont endpoint replay endpointRead →
          Cont candidateRead endpointRead publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row candidateRead ∨ hsame row endpointRead ∨
                      hsame row obstruction ∨ hsame row publicRead)
                  (fun row : BHist =>
                    PkgSig bundle publicRead pkg ∧ hsame row publicRead)
                  hsame ∧
                UnaryHistory candidateRead ∧ UnaryHistory endpointRead ∧
                  UnaryHistory publicRead ∧ Cont candidate closedCandidate candidateRead ∧
                    Cont endpoint replay endpointRead ∧
                      Cont candidateRead endpointRead publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier candidateClosedRead endpointReplayRead candidateEndpointPublic publicPkg
  obtain ⟨candidateUnary, closedCandidateUnary, _finishedUnary, endpointUnary,
    obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed candidateReadUnary endpointReadUnary candidateEndpointPublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row endpointRead ∨ hsame row obstruction ∨
              hsame row publicRead)
          (fun row : BHist => PkgSig bundle publicRead pkg ∧ hsame row publicRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨publicPkg, source.left⟩
    }
  exact
    ⟨cert, candidateReadUnary, endpointReadUnary, publicReadUnary, candidateClosedRead,
      endpointReplayRead, candidateEndpointPublic⟩

theorem MetaCICNormalizationFrontierCarrier_consumer_boundary_lock
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead endpointRead lockedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg →
      Cont candidate closedCandidate candidateRead →
        Cont finished endpoint endpointRead →
          Cont candidateRead endpointRead lockedRead →
            PkgSig bundle lockedRead pkg →
              UnaryHistory candidateRead ∧ UnaryHistory endpointRead ∧
                UnaryHistory obstruction ∧ UnaryHistory lockedRead ∧
                  Cont candidate closedCandidate candidateRead ∧
                    Cont finished endpoint endpointRead ∧
                      Cont candidateRead endpointRead lockedRead ∧
                        PkgSig bundle lockedRead pkg ∧
                          SemanticNameCert
                            (fun row : BHist => hsame row lockedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row candidateRead ∨ hsame row endpointRead ∨
                                hsame row obstruction ∨ hsame row lockedRead)
                            (fun row : BHist =>
                              PkgSig bundle lockedRead pkg ∧ hsame row lockedRead)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier candidateClosedRead finishedEndpointRead candidateEndpointLocked lockedPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    obstructionUnary, _transportUnary, _replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have lockedReadUnary : UnaryHistory lockedRead :=
    unary_cont_closed candidateReadUnary endpointReadUnary candidateEndpointLocked
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row lockedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row candidateRead ∨ hsame row endpointRead ∨ hsame row obstruction ∨
            hsame row lockedRead)
        (fun row : BHist => PkgSig bundle lockedRead pkg ∧ hsame row lockedRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro lockedRead ⟨hsame_refl lockedRead, lockedReadUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨lockedPkg, source.left⟩
    }
  exact
    ⟨candidateReadUnary, endpointReadUnary, obstructionUnary, lockedReadUnary,
      candidateClosedRead, finishedEndpointRead, candidateEndpointLocked, lockedPkg, cert⟩

theorem MetaCICNormalizationFrontierCarrier_candidate_coverage [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont candidateRead replay publicRead ->
          PkgSig bundle publicRead pkg ->
            UnaryHistory candidateRead ∧ UnaryHistory publicRead ∧
              Cont candidate closedCandidate candidateRead ∧
                Cont candidateRead replay publicRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
                    hsame obstruction obstruction := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier candidateClosedRead candidateReplayPublic publicPkg
  obtain ⟨candidateUnary, closedCandidateUnary, _finishedUnary, _endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed candidateReadUnary replayUnary candidateReplayPublic
  exact
    ⟨candidateReadUnary, publicReadUnary, candidateClosedRead, candidateReplayPublic,
      provenancePkg, publicPkg, hsame_refl obstruction⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
