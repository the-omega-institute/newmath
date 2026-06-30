import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditCandidateBoundaryScope [AskSetup] [PackageSetup]
    {R C S A N F H T P L localName scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp R C S A N F H T P L localName bundle pkg →
      Cont R C scopeRead →
        Cont scopeRead S A →
          PkgSig bundle scopeRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row scopeRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                (fun row : BHist =>
                  hsame row R ∨ hsame row C ∨ hsame row S ∨ hsame row A ∨
                    hsame row N ∨ hsame row scopeRead)
                (fun row : BHist =>
                  hsame row scopeRead ∧ Cont R C scopeRead ∧ Cont scopeRead S A ∧
                    PkgSig bundle scopeRead pkg)
                hsame ∧ UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier candidateRoute applicationRoute scopePkg
  obtain ⟨rUnary, cUnary, sUnary, _aUnary, _nUnary, _fUnary, _hUnary, _tUnary,
    _pUnary, _lUnary, _localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit,
    _confluenceAuditLedger, _transportReplaySame, _provenancePkg, _localNamePkg⟩ := carrier
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed rUnary cUnary candidateRoute
  have sourceScope :
      (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row ∧
        PkgSig bundle row pkg) scopeRead := by
    exact ⟨hsame_refl scopeRead, scopeUnary, scopePkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row ∧
            PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row R ∨ hsame row C ∨ hsame row S ∨ hsame row A ∨
              hsame row N ∨ hsame row scopeRead)
          (fun row : BHist =>
            hsame row scopeRead ∧ Cont R C scopeRead ∧ Cont scopeRead S A ∧
              PkgSig bundle scopeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead sourceScope
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
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, candidateRoute, applicationRoute, scopePkg⟩
  }
  exact ⟨cert, scopeUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
