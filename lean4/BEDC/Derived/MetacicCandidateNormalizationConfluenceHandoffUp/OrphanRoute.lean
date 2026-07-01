import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationHandoffOrphanRoute [AskSetup] [PackageSetup]
    {audit candidate endpoint frontier residual decider blocked transport replay provenance
      localName residualRead endpointRead siblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate endpoint
        frontier residual decider blocked transport replay provenance localName bundle pkg →
      Cont candidate frontier residualRead →
        Cont residualRead decider endpointRead →
          Cont endpointRead blocked siblingRead →
            PkgSig bundle siblingRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row siblingRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row candidate ∨ hsame row frontier ∨ hsame row residual ∨
                      hsame row decider ∨ hsame row blocked ∨ hsame row residualRead ∨
                        hsame row endpointRead ∨ hsame row siblingRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont candidate frontier residualRead ∧
                      Cont residualRead decider endpointRead ∧
                        Cont endpointRead blocked siblingRead ∧
                          PkgSig bundle siblingRead pkg)
                  hsame ∧
                UnaryHistory residualRead ∧ UnaryHistory endpointRead ∧
                  UnaryHistory siblingRead := by
  -- BEDC touchpoint anchor: MetacicCandidateNormalizationConfluenceHandoffCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier residualRoute endpointRoute siblingRoute siblingPkg
  obtain ⟨_auditUnary, candidateUnary, _endpointUnary, frontierUnary, _residualUnary,
    deciderUnary, blockedUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _provenancePkg⟩ := carrier
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary frontierUnary residualRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed residualReadUnary deciderUnary endpointRoute
  have siblingReadUnary : UnaryHistory siblingRead :=
    unary_cont_closed endpointReadUnary blockedUnary siblingRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row siblingRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidate ∨ hsame row frontier ∨ hsame row residual ∨
              hsame row decider ∨ hsame row blocked ∨ hsame row residualRead ∨
                hsame row endpointRead ∨ hsame row siblingRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont candidate frontier residualRead ∧
              Cont residualRead decider endpointRead ∧ Cont endpointRead blocked siblingRead ∧
                PkgSig bundle siblingRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro siblingRead ⟨hsame_refl siblingRead, siblingReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, residualRoute, endpointRoute, siblingRoute, siblingPkg⟩
  }
  exact ⟨cert, residualReadUnary, endpointReadUnary, siblingReadUnary⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
