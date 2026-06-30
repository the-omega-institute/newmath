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

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
