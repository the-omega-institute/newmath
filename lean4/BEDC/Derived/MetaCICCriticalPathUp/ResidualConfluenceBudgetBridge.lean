import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualConfluenceBudgetBridge [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName residualRead confluenceRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont obstruction handoff residualRead ->
        Cont residualRead dischargeSocket confluenceRead ->
          Cont confluenceRead route budgetRead ->
            PkgSig bundle budgetRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row residualRead ∨ hsame row confluenceRead ∨
                      hsame row budgetRead)
                  (fun row : BHist =>
                    hsame row obstruction ∨ hsame row handoff ∨
                      hsame row dischargeSocket ∨ hsame row route ∨
                        hsame row provenance ∨ hsame row localName ∨
                          hsame row residualRead ∨ hsame row confluenceRead ∨
                            hsame row budgetRead)
                  (fun row : BHist =>
                    PkgSig bundle budgetRead pkg ∧
                      (hsame row residualRead ∨ hsame row confluenceRead ∨
                        hsame row budgetRead))
                  hsame ∧
                UnaryHistory residualRead ∧ UnaryHistory confluenceRead ∧
                  UnaryHistory budgetRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet obstructionHandoffResidual residualDischargeConfluence confluenceRouteBudget
    budgetPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, _provenancePkg⟩ := packet
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed obstructionUnary handoffUnary obstructionHandoffResidual
  have confluenceUnary : UnaryHistory confluenceRead :=
    unary_cont_closed residualUnary dischargeSocketUnary residualDischargeConfluence
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed confluenceUnary routeUnary confluenceRouteBudget
  have sourceResidual :
      (fun row : BHist =>
        hsame row residualRead ∨ hsame row confluenceRead ∨ hsame row budgetRead)
        residualRead := by
    exact Or.inl (hsame_refl residualRead)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row residualRead ∨ hsame row confluenceRead ∨ hsame row budgetRead)
          (fun row : BHist =>
            hsame row obstruction ∨ hsame row handoff ∨ hsame row dischargeSocket ∨
              hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                hsame row residualRead ∨ hsame row confluenceRead ∨ hsame row budgetRead)
          (fun row : BHist =>
            PkgSig bundle budgetRead pkg ∧
              (hsame row residualRead ∨ hsame row confluenceRead ∨ hsame row budgetRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro residualRead sourceResidual
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
        cases source with
        | inl sameResidual =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameResidual)
        | inr rest =>
            cases rest with
            | inl sameConfluence =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameConfluence))
            | inr sameBudget =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameBudget))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameResidual =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameResidual))))))
      | inr rest =>
          cases rest with
          | inl sameConfluence =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inl sameConfluence)))))))
          | inr sameBudget =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inr sameBudget)))))))
    ledger_sound := by
      intro _row source
      exact ⟨budgetPkg, source⟩
  }
  exact ⟨cert, residualUnary, confluenceUnary, budgetUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
