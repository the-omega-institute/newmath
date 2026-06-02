import BEDC.Derived.AuditSystemUp.TasteGate

namespace BEDC.Derived.AuditSystemUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuditSystemCertificateConflictDeterminacy [AskSetup] [PackageSetup]
    {C P F R E L H K Q N conflict gradeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditSystemCarrier C P F R E L H K Q N bundle pkg →
      Cont F R conflict →
        Cont conflict E gradeRead →
          PkgSig bundle Q pkg →
            SemanticNameCert
                (fun row : BHist => hsame row gradeRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row F ∨ hsame row R ∨ hsame row E ∨ hsame row conflict ∨
                    hsame row gradeRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont F R conflict ∧ Cont conflict E gradeRead ∧
                    PkgSig bundle Q pkg)
                hsame ∧
              UnaryHistory conflict ∧ UnaryHistory gradeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier conflictRoute gradeRoute qPkg
  obtain ⟨_cUnary, _pUnary, fUnary, rUnary, eUnary, _lUnary, _hUnary, _kUnary,
    _qUnary, _nUnary, _failureRefusal, _claimPositive, _exportLedger, _carrierPkg⟩ :=
    carrier
  have conflictUnary : UnaryHistory conflict :=
    unary_cont_closed fUnary rUnary conflictRoute
  have gradeUnary : UnaryHistory gradeRead :=
    unary_cont_closed conflictUnary eUnary gradeRoute
  have sourceGrade :
      (fun row : BHist => hsame row gradeRead ∧ UnaryHistory row) gradeRead := by
    exact ⟨hsame_refl gradeRead, gradeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gradeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row R ∨ hsame row E ∨ hsame row conflict ∨
              hsame row gradeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F R conflict ∧ Cont conflict E gradeRead ∧
              PkgSig bundle Q pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro gradeRead sourceGrade
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, conflictRoute, gradeRoute, qPkg⟩
  }
  exact ⟨cert, conflictUnary, gradeUnary⟩

end BEDC.Derived.AuditSystemUp
