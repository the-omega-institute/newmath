import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicFiniteConversionEndpointHandoff [AskSetup] [PackageSetup]
    {audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName endpointRead residualRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate
        normalEndpoint frontier confluence decidability blocked transport replay provenance
        localName bundle pkg →
      Cont normalEndpoint frontier endpointRead →
        Cont endpointRead blocked residualRead →
          PkgSig bundle residualRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row candidate ∨ hsame row normalEndpoint ∨ hsame row frontier ∨
                    hsame row blocked ∨ hsame row endpointRead ∨ hsame row residualRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont normalEndpoint frontier endpointRead ∧
                    Cont endpointRead blocked residualRead ∧ PkgSig bundle residualRead pkg)
                hsame ∧
              UnaryHistory endpointRead ∧ UnaryHistory residualRead := by
  -- BEDC touchpoint anchor: MetacicCandidateNormalizationConfluenceHandoffCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier endpointRoute residualRoute residualPkg
  obtain ⟨_auditUnary, _candidateUnary, endpointUnary, frontierUnary, _confluenceUnary,
    _decidableUnary, blockedUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _provenancePkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary frontierUnary endpointRoute
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed endpointReadUnary blockedUnary residualRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidate ∨ hsame row normalEndpoint ∨ hsame row frontier ∨
              hsame row blocked ∨ hsame row endpointRead ∨ hsame row residualRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont normalEndpoint frontier endpointRead ∧
              Cont endpointRead blocked residualRead ∧ PkgSig bundle residualRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro residualRead ⟨hsame_refl residualRead, residualReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointRoute, residualRoute, residualPkg⟩
  }
  exact ⟨cert, endpointReadUnary, residualReadUnary⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
