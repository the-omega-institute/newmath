import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_audit_map_handoff [AskSetup] [PackageSetup]
    {M A L I R H C P N auditRead dependencyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont R C auditRead →
        Cont auditRead P dependencyRead →
          PkgSig bundle dependencyRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row dependencyRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
                    hsame row R ∨ hsame row dependencyRead)
                (fun _row : BHist =>
                  PkgSig bundle dependencyRead pkg ∧ Cont R C auditRead ∧
                    Cont auditRead P dependencyRead)
                hsame ∧
              UnaryHistory auditRead ∧ UnaryHistory dependencyRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier auditRoute dependencyRoute dependencyPkg
  obtain ⟨_mUnary, _aUnary, _lUnary, _iUnary, rUnary, _hUnary, cUnary, pUnary,
    _nUnary, _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer,
    _namePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed rUnary cUnary auditRoute
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed auditUnary pUnary dependencyRoute
  have sourceAtDependency :
      hsame dependencyRead dependencyRead ∧ UnaryHistory dependencyRead :=
    ⟨hsame_refl dependencyRead, dependencyUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dependencyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
              hsame row R ∨ hsame row dependencyRead)
          (fun _row : BHist =>
            PkgSig bundle dependencyRead pkg ∧ Cont R C auditRead ∧
              Cont auditRead P dependencyRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro dependencyRead sourceAtDependency
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
      intro _row _source
      exact ⟨dependencyPkg, auditRoute, dependencyRoute⟩
  }
  exact ⟨cert, auditUnary, dependencyUnary⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
