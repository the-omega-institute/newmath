import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_audit_map_consumer_totality [AskSetup] [PackageSetup]
    {M A L I R H C P N verdictRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont R H verdictRead →
        Cont verdictRead C auditRead →
          PkgSig bundle auditRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
                    hsame row R ∨ hsame row auditRead)
                (fun row : BHist => PkgSig bundle auditRead pkg ∧ hsame row auditRead)
                hsame ∧
              UnaryHistory verdictRead ∧ UnaryHistory auditRead ∧ Cont R H verdictRead ∧
                Cont verdictRead C auditRead ∧ PkgSig bundle N pkg ∧
                  PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier verdictRoute auditRoute auditPkg
  obtain ⟨_mUnary, _aUnary, _lUnary, _iUnary, rUnary, hUnary, cUnary, _pUnary,
    _nUnary, _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer,
    namePkg⟩ := carrier
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed rUnary hUnary verdictRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed verdictUnary cUnary auditRoute
  have sourceAtAudit : hsame auditRead auditRead ∧ UnaryHistory auditRead :=
    ⟨hsame_refl auditRead, auditUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
              hsame row R ∨ hsame row auditRead)
          (fun row : BHist => PkgSig bundle auditRead pkg ∧ hsame row auditRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead sourceAtAudit
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
      exact ⟨auditPkg, source.left⟩
  }
  exact ⟨cert, verdictUnary, auditUnary, verdictRoute, auditRoute, namePkg, auditPkg⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
