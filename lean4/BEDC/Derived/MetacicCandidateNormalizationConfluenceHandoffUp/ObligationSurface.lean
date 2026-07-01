import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceHandoffObligationSurface
    [AskSetup] [PackageSetup]
    {A K N F C D B T R P L endpointRead frontierRead residualRead deciderRead
      surfaceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier A K N F C D B T R P
        L bundle pkg ->
      Cont K N endpointRead ->
        Cont endpointRead F frontierRead ->
          Cont frontierRead C residualRead ->
            Cont residualRead D deciderRead ->
              Cont deciderRead B surfaceRead ->
                PkgSig bundle surfaceRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row surfaceRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row A ∨ hsame row K ∨ hsame row N ∨ hsame row F ∨
                          hsame row C ∨ hsame row D ∨ hsame row B ∨ hsame row T ∨
                            hsame row R ∨ hsame row P ∨ hsame row L ∨
                              hsame row surfaceRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont K N endpointRead ∧
                          Cont endpointRead F frontierRead ∧
                            Cont frontierRead C residualRead ∧
                              Cont residualRead D deciderRead ∧
                                Cont deciderRead B surfaceRead ∧
                                  PkgSig bundle surfaceRead pkg)
                      hsame ∧
                    UnaryHistory endpointRead ∧ UnaryHistory frontierRead ∧
                      UnaryHistory residualRead ∧ UnaryHistory deciderRead ∧
                        UnaryHistory surfaceRead := by
  -- BEDC touchpoint anchor: MetacicCandidateNormalizationConfluenceHandoffCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier endpointRoute frontierRoute residualRoute deciderRoute surfaceRoute surfacePkg
  obtain ⟨_auditUnary, candidateUnary, endpointUnary, frontierUnary, residualUnary,
    decidableUnary, blockedUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _provenancePkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed candidateUnary endpointUnary endpointRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed endpointReadUnary frontierUnary frontierRoute
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed frontierReadUnary residualUnary residualRoute
  have deciderReadUnary : UnaryHistory deciderRead :=
    unary_cont_closed residualReadUnary decidableUnary deciderRoute
  have surfaceReadUnary : UnaryHistory surfaceRead :=
    unary_cont_closed deciderReadUnary blockedUnary surfaceRoute
  constructor
  · constructor
    · constructor
      · exact Exists.intro surfaceRead ⟨hsame_refl surfaceRead, surfaceReadUnary⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other sameRows
        exact hsame_symm sameRows
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    · intro _row sourceRow
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact sourceRow.left
    · intro _row sourceRow
      exact
        ⟨sourceRow.right, endpointRoute, frontierRoute, residualRoute, deciderRoute,
          surfaceRoute, surfacePkg⟩
  · exact
      ⟨endpointReadUnary, frontierReadUnary, residualReadUnary, deciderReadUnary,
        surfaceReadUnary⟩

theorem MetacicCandidateHandoffScopedTasteGateRoute [AskSetup] [PackageSetup]
    {A K N F C D B T R P L frontierRead boundaryRead joinRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier A K N F C D B T R P
        L bundle pkg ->
      Cont A K frontierRead ->
        Cont frontierRead F boundaryRead ->
          Cont C D joinRead ->
            PkgSig bundle P pkg ->
              PkgSig bundle boundaryRead pkg ->
                PkgSig bundle joinRead pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row boundaryRead ∨ hsame row joinRead) ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row A ∨ hsame row K ∨ hsame row N ∨ hsame row F ∨
                          hsame row C ∨ hsame row D ∨ hsame row B ∨ hsame row T ∨
                            hsame row R ∨ hsame row P ∨ hsame row L ∨
                              hsame row boundaryRead ∨ hsame row joinRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont A K frontierRead ∧
                          Cont frontierRead F boundaryRead ∧ Cont C D joinRead ∧
                            PkgSig bundle P pkg)
                      hsame ∧
                    UnaryHistory boundaryRead ∧ UnaryHistory joinRead := by
  -- BEDC touchpoint anchor: MetacicCandidateNormalizationConfluenceHandoffCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier frontierRoute boundaryRoute joinRoute provenancePkg _boundaryPkg _joinPkg
  obtain ⟨auditUnary, candidateUnary, _normalUnary, frontierUnary, confluenceUnary,
    decidableUnary, _blockedUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _carrierPkg⟩ := carrier
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed auditUnary candidateUnary frontierRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed frontierReadUnary frontierUnary boundaryRoute
  have joinReadUnary : UnaryHistory joinRead :=
    unary_cont_closed confluenceUnary decidableUnary joinRoute
  constructor
  · constructor
    · constructor
      · exact
          Exists.intro boundaryRead
            ⟨Or.inl (hsame_refl boundaryRead), boundaryReadUnary⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other sameRows
        exact hsame_symm sameRows
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other sameRows sourceRow
        exact
          ⟨Or.elim sourceRow.left
              (fun sameBoundary =>
                Or.inl (hsame_trans (hsame_symm sameRows) sameBoundary))
              (fun sameJoin =>
                Or.inr (hsame_trans (hsame_symm sameRows) sameJoin)),
            unary_transport sourceRow.right sameRows⟩
    · intro _row sourceRow
      cases sourceRow.left with
      | inl sameBoundary =>
          right; right; right; right; right; right; right; right; right; right; right; left
          exact sameBoundary
      | inr sameJoin =>
          right; right; right; right; right; right; right; right; right; right; right; right
          exact sameJoin
    · intro _row sourceRow
      exact
        ⟨sourceRow.right, frontierRoute, boundaryRoute, joinRoute, provenancePkg⟩
  · exact ⟨boundaryReadUnary, joinReadUnary⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
