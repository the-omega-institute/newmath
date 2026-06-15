import BEDC.Derived.MetaCICSubjectReductionBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.MetaCICSubjectReductionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem MetaCICSubjectReductionBoundary_namecert_obligations [AskSetup] [PackageSetup]
    {beta app lam pi preservation obstruction audit transport route provenance name consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont beta app route ->
      Cont lam pi preservation ->
        hsame transport (append route audit) ->
          PkgSig bundle consumer pkg ->
            SemanticNameCert
              (fun row : BHist =>
                hsame row consumer ∧
                  ∃ packet : MetaCICSubjectReductionBoundaryUp,
                    packet = MetaCICSubjectReductionBoundaryUp.mk beta app lam pi preservation
                      obstruction audit transport route provenance name)
              (fun row : BHist =>
                Cont beta app route ∧ Cont lam pi preservation ∧
                  hsame transport (append route audit) ∧ hsame row consumer)
              (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro betaApp lamPi transportAudit consumerPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro consumer
          ⟨hsame_refl consumer,
            Exists.intro
              (MetaCICSubjectReductionBoundaryUp.mk beta app lam pi preservation obstruction
                audit transport route provenance name)
              rfl⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨betaApp, lamPi, transportAudit, sourceRow.left⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, consumerPkg⟩
  }

end BEDC.Derived.MetaCICSubjectReductionBoundaryUp
