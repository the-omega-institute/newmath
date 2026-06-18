import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierCarrier_candidate_evidence_totality
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead sealedRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont candidateRead obstruction sealedRead ->
          Cont sealedRead replay routeRead ->
            PkgSig bundle routeRead pkg ->
              UnaryHistory candidateRead ∧ UnaryHistory sealedRead ∧
                UnaryHistory routeRead ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row candidateRead ∨ hsame row sealedRead ∨
                        hsame row routeRead)
                    (fun row : BHist =>
                      PkgSig bundle routeRead pkg ∧ hsame row routeRead)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier candidateClosedRead candidateObstructionSeal sealedReplayRoute routePkg
  obtain ⟨candidateUnary, closedCandidateUnary, _finishedUnary, _endpointUnary,
    obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have sealedReadUnary : UnaryHistory sealedRead :=
    unary_cont_closed candidateReadUnary obstructionUnary candidateObstructionSeal
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed sealedReadUnary replayUnary sealedReplayRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row candidateRead ∨ hsame row sealedRead ∨ hsame row routeRead)
        (fun row : BHist => PkgSig bundle routeRead pkg ∧ hsame row routeRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro routeRead ⟨hsame_refl routeRead, routeReadUnary⟩
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
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨routePkg, source.left⟩
    }
  exact ⟨candidateReadUnary, sealedReadUnary, routeReadUnary, cert⟩

theorem MetaCICNormalizationFrontierCarrier_root_candidate_readback
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont candidateRead replay rootRead ->
          PkgSig bundle rootRead pkg ->
            UnaryHistory candidateRead ∧ UnaryHistory rootRead ∧
              SemanticNameCert
                (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row candidate ∨ hsame row closedCandidate ∨
                    hsame row candidateRead ∨ hsame row rootRead)
                (fun row : BHist => PkgSig bundle rootRead pkg ∧ hsame row rootRead)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier candidateClosedRead candidateReplayRoot rootPkg
  obtain ⟨candidateUnary, closedCandidateUnary, _finishedUnary, _endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed candidateReadUnary replayUnary candidateReplayRoot
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row candidate ∨ hsame row closedCandidate ∨
            hsame row candidateRead ∨ hsame row rootRead)
        (fun row : BHist => PkgSig bundle rootRead pkg ∧ hsame row rootRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro rootRead ⟨hsame_refl rootRead, rootReadUnary⟩
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
        exact ⟨rootPkg, source.left⟩
    }
  exact ⟨candidateReadUnary, rootReadUnary, cert⟩

theorem MetaCICNormalizationFrontierCarrier_candidate_route_totality
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
      Cont candidateRead replay routeRead ->
      PkgSig bundle routeRead pkg ->
        UnaryHistory candidate ∧ UnaryHistory closedCandidate ∧
          UnaryHistory candidateRead ∧ UnaryHistory routeRead ∧
            Cont candidate closedCandidate candidateRead ∧
              Cont candidateRead replay routeRead ∧ PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier candidateClosedRead candidateReplayRoute routePkg
  obtain ⟨candidateUnary, closedCandidateUnary, _finishedUnary, _endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed candidateReadUnary replayUnary candidateReplayRoute
  exact
    ⟨candidateUnary, closedCandidateUnary, candidateReadUnary, routeReadUnary,
      candidateClosedRead, candidateReplayRoute, routePkg⟩

theorem MetaCICNormalizationFrontierCarrier_candidate_sn_consumer_route
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead endpointRead auditRead closedRead snRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg ->
      Cont candidate closedCandidate candidateRead ->
        Cont finished endpoint endpointRead ->
          Cont candidateRead replay auditRead ->
            Cont endpointRead provenance closedRead ->
              Cont auditRead closedRead snRead ->
                PkgSig bundle snRead pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row snRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row candidateRead ∨ hsame row endpointRead ∨
                        hsame row auditRead ∨ hsame row closedRead ∨ hsame row snRead)
                    (fun row : BHist => PkgSig bundle snRead pkg ∧ hsame row snRead)
                    hsame ∧
                    UnaryHistory candidateRead ∧ UnaryHistory endpointRead ∧
                      UnaryHistory auditRead ∧ UnaryHistory closedRead ∧
                        UnaryHistory snRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier candidateClosedRead finishedEndpointRead candidateReplayAudit
    endpointProvenanceClosed auditClosedSn snPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, provenanceUnary, _localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    _transportSameCandidateFinished, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed candidateReadUnary replayUnary candidateReplayAudit
  have closedReadUnary : UnaryHistory closedRead :=
    unary_cont_closed endpointReadUnary provenanceUnary endpointProvenanceClosed
  have snReadUnary : UnaryHistory snRead :=
    unary_cont_closed auditReadUnary closedReadUnary auditClosedSn
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row snRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row candidateRead ∨ hsame row endpointRead ∨
            hsame row auditRead ∨ hsame row closedRead ∨ hsame row snRead)
        (fun row : BHist => PkgSig bundle snRead pkg ∧ hsame row snRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro snRead ⟨hsame_refl snRead, snReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨snPkg, source.left⟩
    }
  exact
    ⟨cert, candidateReadUnary, endpointReadUnary, auditReadUnary, closedReadUnary,
      snReadUnary⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
