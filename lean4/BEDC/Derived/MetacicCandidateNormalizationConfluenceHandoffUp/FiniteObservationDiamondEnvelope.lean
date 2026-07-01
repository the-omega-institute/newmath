import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationMetaCICDiamondEnvelopeNameCertObligations
    [AskSetup] [PackageSetup]
    {A K N F C D B T R P L endpointRead residualRead deciderRead blockedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier A K N F C D B T R P L
        bundle pkg ->
      Cont K N endpointRead ->
        Cont endpointRead C residualRead ->
          Cont residualRead D deciderRead ->
            Cont deciderRead B blockedRead ->
              PkgSig bundle blockedRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row blockedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row N ∨ hsame row C ∨ hsame row D ∨
                        hsame row B ∨ hsame row endpointRead ∨ hsame row residualRead ∨
                          hsame row deciderRead ∨ hsame row blockedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont K N endpointRead ∧
                        Cont endpointRead C residualRead ∧
                          Cont residualRead D deciderRead ∧
                            Cont deciderRead B blockedRead ∧
                              PkgSig bundle blockedRead pkg)
                    hsame ∧
                  UnaryHistory endpointRead ∧ UnaryHistory residualRead ∧
                    UnaryHistory deciderRead ∧ UnaryHistory blockedRead := by
  -- BEDC touchpoint anchor: MetacicCandidateNormalizationConfluenceHandoffCarrier BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier endpointRoute residualRoute deciderRoute blockedRoute blockedPkg
  obtain ⟨_auditUnary, candidateUnary, normalEndpointUnary, _frontierUnary,
    confluenceUnary, decidabilityUnary, blockedUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _provenancePkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed candidateUnary normalEndpointUnary endpointRoute
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed endpointReadUnary confluenceUnary residualRoute
  have deciderReadUnary : UnaryHistory deciderRead :=
    unary_cont_closed residualReadUnary decidabilityUnary deciderRoute
  have blockedReadUnary : UnaryHistory blockedRead :=
    unary_cont_closed deciderReadUnary blockedUnary blockedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row blockedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row N ∨ hsame row C ∨ hsame row D ∨
              hsame row B ∨ hsame row endpointRead ∨ hsame row residualRead ∨
                hsame row deciderRead ∨ hsame row blockedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K N endpointRead ∧
              Cont endpointRead C residualRead ∧
                Cont residualRead D deciderRead ∧
                  Cont deciderRead B blockedRead ∧ PkgSig bundle blockedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro blockedRead ⟨hsame_refl blockedRead, blockedReadUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, endpointRoute, residualRoute, deciderRoute, blockedRoute,
          blockedPkg⟩
  }
  exact
    ⟨cert, endpointReadUnary, residualReadUnary, deciderReadUnary,
      blockedReadUnary⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
