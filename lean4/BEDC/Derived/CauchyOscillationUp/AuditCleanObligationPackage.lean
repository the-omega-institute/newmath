import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationAuditCleanObligationPackage [AskSetup] [PackageSetup]
    {W M Q T S H C P N auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg ->
      Cont W M Q ->
        Cont Q T auditRead ->
          PkgSig bundle auditRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨
                    hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N ∨ hsame row auditRead)
                (fun row : BHist =>
                  hsame row auditRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle auditRead pkg)
                hsame ∧ UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier _displayedRoot auditRoute auditPkg
  obtain ⟨_wUnary, _mUnary, qUnary, tUnary, _sUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _tailModulus, _modulusTolerance, _ledgerSeal, _routesNameCert,
    provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed qUnary tUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨
              hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row auditRead)
          (fun row : BHist =>
            hsame row auditRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle auditRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead ⟨hsame_refl auditRead, auditUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, provenancePkg, auditPkg⟩
  }
  exact ⟨cert, auditUnary⟩

end BEDC.Derived.CauchyOscillationUp
