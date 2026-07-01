import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceHandoffResidualDiamondTotality
    [AskSetup] [PackageSetup]
    {A K N F C D B T R P L endpointRead residualRead diamondRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier A K N F C D B T R P L
        bundle pkg →
      Cont K N endpointRead →
        Cont endpointRead C residualRead →
          Cont residualRead B diamondRead →
            PkgSig bundle diamondRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row diamondRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row K ∨ hsame row N ∨ hsame row C ∨ hsame row B ∨
                      hsame row endpointRead ∨ hsame row residualRead ∨
                        hsame row diamondRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont K N endpointRead ∧
                      Cont endpointRead C residualRead ∧
                        Cont residualRead B diamondRead ∧ PkgSig bundle diamondRead pkg)
                  hsame ∧ UnaryHistory endpointRead ∧ UnaryHistory residualRead ∧
                    UnaryHistory diamondRead := by
  -- BEDC touchpoint anchor: MetacicCandidateNormalizationConfluenceHandoffCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier endpointRoute residualRoute diamondRoute diamondPkg
  obtain ⟨_auditUnary, candidateUnary, normalEndpointUnary, _frontierUnary,
    confluenceUnary, _decidabilityUnary, blockedUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _provenancePkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed candidateUnary normalEndpointUnary endpointRoute
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed endpointReadUnary confluenceUnary residualRoute
  have diamondReadUnary : UnaryHistory diamondRead :=
    unary_cont_closed residualReadUnary blockedUnary diamondRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row diamondRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row N ∨ hsame row C ∨ hsame row B ∨
              hsame row endpointRead ∨ hsame row residualRead ∨ hsame row diamondRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K N endpointRead ∧
              Cont endpointRead C residualRead ∧
                Cont residualRead B diamondRead ∧ PkgSig bundle diamondRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro diamondRead ⟨hsame_refl diamondRead, diamondReadUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      right
      right
      right
      right
      right
      right
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, endpointRoute, residualRoute, diamondRoute, diamondPkg⟩
  }
  exact ⟨cert, endpointReadUnary, residualReadUnary, diamondReadUnary⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
