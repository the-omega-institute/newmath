import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem MetaCICNormalizationFrontierGroundCompilerRoute [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead endpointRead normalRead substitutionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg →
      Cont candidate closedCandidate candidateRead →
        Cont finished endpoint finishedRead →
          Cont finishedRead replay endpointRead →
            Cont endpointRead localRow normalRead →
              Cont endpoint replay endpointRead →
                Cont endpointRead localRow substitutionRead →
                  PkgSig bundle normalRead pkg →
                    PkgSig bundle substitutionRead pkg →
                      UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                        UnaryHistory endpointRead ∧ UnaryHistory normalRead ∧
                          UnaryHistory substitutionRead ∧
                            hsame transport (append candidate finished) ∧
                              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead finishedReplayEndpoint
    endpointLocalNormal _endpointReplayEndpoint endpointLocalSubstitution _normalPkg
    _substitutionPkg
  obtain ⟨candidateUnary, closedCandidateUnary, finishedUnary, endpointUnary,
    _obstructionUnary, _transportUnary, replayUnary, _provenanceUnary, localRowUnary,
    _candidateClosedLocal, _finishedEndpointReplay, _endpointReplayProvenance,
    transportSameCandidateFinished, provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed candidateUnary closedCandidateUnary candidateClosedRead
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed finishedUnary endpointUnary finishedEndpointRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed finishedReadUnary replayUnary finishedReplayEndpoint
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed endpointReadUnary localRowUnary endpointLocalNormal
  have substitutionReadUnary : UnaryHistory substitutionRead :=
    unary_cont_closed endpointReadUnary localRowUnary endpointLocalSubstitution
  exact
    ⟨candidateReadUnary, finishedReadUnary, endpointReadUnary, normalReadUnary,
      substitutionReadUnary, transportSameCandidateFinished, provenancePkg⟩

theorem MetaCICNormalizationFrontierTasteGateRoute [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead endpointRead normalRead substitutionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
        transport replay provenance localRow bundle pkg →
      Cont candidate closedCandidate candidateRead →
        Cont finished endpoint finishedRead →
          Cont finishedRead replay endpointRead →
            Cont endpointRead localRow normalRead →
              Cont endpoint replay endpointRead →
                Cont endpointRead localRow substitutionRead →
                  PkgSig bundle normalRead pkg →
                    PkgSig bundle substitutionRead pkg →
                      metaCICNormalizationFrontierFromEventFlow
                          (metaCICNormalizationFrontierToEventFlow
                            (MetaCICNormalizationFrontierUp.mk candidate closedCandidate
                              finished endpoint obstruction transport replay provenance
                              localRow)) =
                        some
                          (MetaCICNormalizationFrontierUp.mk candidate closedCandidate
                            finished endpoint obstruction transport replay provenance localRow) ∧
                        UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧
                          UnaryHistory endpointRead ∧ UnaryHistory normalRead ∧
                            UnaryHistory substitutionRead ∧
                              hsame transport (append candidate finished) ∧
                                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier candidateClosedRead finishedEndpointRead finishedReplayEndpoint
    endpointLocalNormal endpointReplayEndpoint endpointLocalSubstitution normalPkg
    substitutionPkg
  have route :=
    MetaCICNormalizationFrontierGroundCompilerRoute
      (candidate := candidate) (closedCandidate := closedCandidate) (finished := finished)
      (endpoint := endpoint) (obstruction := obstruction) (transport := transport)
      (replay := replay) (provenance := provenance) (localRow := localRow)
      (candidateRead := candidateRead) (finishedRead := finishedRead)
      (endpointRead := endpointRead) (normalRead := normalRead)
      (substitutionRead := substitutionRead) (bundle := bundle) (pkg := pkg)
      carrier candidateClosedRead finishedEndpointRead finishedReplayEndpoint
      endpointLocalNormal endpointReplayEndpoint endpointLocalSubstitution normalPkg
      substitutionPkg
  have roundTrip :
      metaCICNormalizationFrontierFromEventFlow
          (metaCICNormalizationFrontierToEventFlow
            (MetaCICNormalizationFrontierUp.mk candidate closedCandidate finished endpoint
              obstruction transport replay provenance localRow)) =
        some
          (MetaCICNormalizationFrontierUp.mk candidate closedCandidate finished endpoint
            obstruction transport replay provenance localRow) := by
    change
      BHistCarrier.fromEventFlow
          (BHistCarrier.toEventFlow
            (MetaCICNormalizationFrontierUp.mk candidate closedCandidate finished endpoint
              obstruction transport replay provenance localRow)) =
        some
          (MetaCICNormalizationFrontierUp.mk candidate closedCandidate finished endpoint
            obstruction transport replay provenance localRow)
    exact BEDC.Meta.TasteGate.ChapterTasteGate.round_trip
      (MetaCICNormalizationFrontierUp.mk candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow)
  exact ⟨roundTrip, route⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
