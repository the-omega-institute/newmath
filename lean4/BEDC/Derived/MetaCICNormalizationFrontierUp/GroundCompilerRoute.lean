import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

def MetaCICNormalizationFrontierGroundCompilerFormalTarget [AskSetup] [PackageSetup]
    (candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead endpointRead normalRead substitutionRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint obstruction
      transport replay provenance localRow bundle pkg ∧
    Cont candidate closedCandidate candidateRead ∧
      Cont finished endpoint finishedRead ∧
        Cont finishedRead replay endpointRead ∧
          Cont endpointRead localRow normalRead ∧
            Cont endpoint replay endpointRead ∧
              Cont endpointRead localRow substitutionRead ∧
                PkgSig bundle normalRead pkg ∧ PkgSig bundle substitutionRead pkg

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

theorem MetaCICNormalizationFrontierGroundCompilerTargetScope [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead finishedRead endpointRead normalRead substitutionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierGroundCompilerFormalTarget candidate closedCandidate finished
        endpoint obstruction transport replay provenance localRow candidateRead finishedRead
        endpointRead normalRead substitutionRead bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            MetaCICNormalizationFrontierGroundCompilerFormalTarget candidate closedCandidate
              finished endpoint obstruction transport replay provenance localRow candidateRead
              finishedRead endpointRead normalRead substitutionRead bundle pkg ∧
              hsame row normalRead)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row finishedRead ∨ hsame row endpointRead ∨
              hsame row normalRead ∨ hsame row substitutionRead)
          (fun row : BHist =>
            PkgSig bundle normalRead pkg ∧ PkgSig bundle substitutionRead pkg ∧
              hsame row normalRead)
          hsame ∧
        UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧ UnaryHistory endpointRead ∧
          UnaryHistory normalRead ∧ UnaryHistory substitutionRead ∧
            hsame transport (append candidate finished) ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro target
  have targetPacket :
      MetaCICNormalizationFrontierGroundCompilerFormalTarget candidate closedCandidate finished
        endpoint obstruction transport replay provenance localRow candidateRead finishedRead
        endpointRead normalRead substitutionRead bundle pkg :=
    target
  obtain ⟨carrier, candidateClosedRead, finishedEndpointRead, finishedReplayEndpoint,
    endpointLocalNormal, endpointReplayEndpoint, endpointLocalSubstitution, normalPkg,
    substitutionPkg⟩ := target
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
  have routePacket :
      UnaryHistory candidateRead ∧ UnaryHistory finishedRead ∧ UnaryHistory endpointRead ∧
        UnaryHistory normalRead ∧ UnaryHistory substitutionRead ∧
          hsame transport (append candidate finished) ∧ PkgSig bundle provenance pkg :=
    route
  obtain ⟨_candidateReadUnary, _finishedReadUnary, _endpointReadUnary, _normalReadUnary,
    _substitutionReadUnary, _transportSameCandidateFinished, _provenancePkg⟩ := route
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            MetaCICNormalizationFrontierGroundCompilerFormalTarget candidate closedCandidate
              finished endpoint obstruction transport replay provenance localRow candidateRead
              finishedRead endpointRead normalRead substitutionRead bundle pkg ∧
              hsame row normalRead)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row finishedRead ∨ hsame row endpointRead ∨
              hsame row normalRead ∨ hsame row substitutionRead)
          (fun row : BHist =>
            PkgSig bundle normalRead pkg ∧ PkgSig bundle substitutionRead pkg ∧
              hsame row normalRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro normalRead ⟨targetPacket, hsame_refl normalRead⟩
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
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inl source.right)))
      ledger_sound := by
        intro _row source
        exact ⟨normalPkg, substitutionPkg, source.right⟩
    }
  exact ⟨cert, routePacket⟩

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
