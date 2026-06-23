import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditRefusalScope [AskSetup] [PackageSetup]
    {R C S A N F H T P L localName refusalRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp R C S A N F H T P L localName bundle pkg →
      Cont N F refusalRead →
        Cont refusalRead T named →
          PkgSig bundle named pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row named ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                (fun row : BHist =>
                  hsame row N ∨ hsame row F ∨ hsame row T ∨ hsame row refusalRead ∨
                    hsame row named ∨ hsame row L)
                (fun row : BHist =>
                  hsame row named ∧ Cont N F refusalRead ∧
                    Cont refusalRead T named ∧ PkgSig bundle L pkg)
                hsame ∧ UnaryHistory refusalRead ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: MetacicNormalizationAuditUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier refusalRoute namedRoute namedPkg
  obtain ⟨_rUnary, _cUnary, _sUnary, _aUnary, nUnary, fUnary, _hUnary, tUnary,
    _pUnary, _lUnary, _localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit,
    _confluenceAuditLedger, _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed nUnary fUnary refusalRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed refusalUnary tUnary namedRoute
  have sourceNamed :
      (fun row : BHist => hsame row named ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        named := by
    exact ⟨hsame_refl named, namedUnary, namedPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row named ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row N ∨ hsame row F ∨ hsame row T ∨ hsame row refusalRead ∨
              hsame row named ∨ hsame row L)
          (fun row : BHist =>
            hsame row named ∧ Cont N F refusalRead ∧ Cont refusalRead T named ∧
              PkgSig bundle L pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named sourceNamed
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, refusalRoute, namedRoute, provenancePkg⟩
  }
  exact ⟨cert, refusalUnary, namedUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
