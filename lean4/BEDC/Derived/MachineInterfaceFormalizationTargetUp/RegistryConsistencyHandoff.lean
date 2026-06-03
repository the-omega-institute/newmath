import BEDC.Derived.MachineInterfaceFormalizationTargetUp.TasteGate

namespace BEDC.Derived.MachineInterfaceFormalizationTargetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MachineInterfaceFormalizationTarget_registry_consistency_handoff
    [AskSetup] [PackageSetup]
    {targetName namespaceRow registry statementSkeleton dependencyList expectedStatus auditGate
      notClaimed _transport _continuation provenance _localName registryRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont registry statementSkeleton registryRead →
      Cont registryRead dependencyList exportRead →
        PkgSig bundle provenance pkg →
          UnaryHistory registry →
            UnaryHistory statementSkeleton →
              UnaryHistory dependencyList →
                SemanticNameCert
                    (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row targetName ∨ hsame row namespaceRow ∨ hsame row registry ∨
                        hsame row statementSkeleton ∨ hsame row dependencyList ∨
                          hsame row expectedStatus ∨ hsame row auditGate ∨
                            hsame row notClaimed ∨ hsame row registryRead ∨
                              hsame row exportRead)
                    (fun row : BHist => hsame row exportRead ∧ PkgSig bundle provenance pkg)
                    hsame ∧
                  UnaryHistory registryRead ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro registryCont exportCont provenancePkg registryUnary statementUnary dependencyUnary
  have registryReadUnary : UnaryHistory registryRead :=
    unary_cont_closed registryUnary statementUnary registryCont
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed registryReadUnary dependencyUnary exportCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row targetName ∨ hsame row namespaceRow ∨ hsame row registry ∨
              hsame row statementSkeleton ∨ hsame row dependencyList ∨
                hsame row expectedStatus ∨ hsame row auditGate ∨ hsame row notClaimed ∨
                  hsame row registryRead ∨ hsame row exportRead)
          (fun row : BHist => hsame row exportRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro exportRead ⟨hsame_refl exportRead, exportReadUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact ⟨cert, registryReadUnary, exportReadUnary⟩

end BEDC.Derived.MachineInterfaceFormalizationTargetUp
