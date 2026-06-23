import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditFrontierFormalTarget [AskSetup] [PackageSetup]
    {R C S A N F H T P L localName candidateRead frontierRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp R C S A N F H T P L localName bundle pkg →
      Cont R C candidateRead →
        Cont candidateRead S frontierRead →
          Cont frontierRead A publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row publicRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                  (fun row : BHist =>
                    hsame row R ∨ hsame row C ∨ hsame row S ∨ hsame row A ∨
                      hsame row N ∨ hsame row candidateRead ∨
                        hsame row frontierRead ∨ hsame row publicRead)
                  (fun row : BHist =>
                    hsame row publicRead ∧ Cont R C candidateRead ∧
                      Cont candidateRead S frontierRead ∧
                        Cont frontierRead A publicRead ∧ PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory candidateRead ∧ UnaryHistory frontierRead ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: MetacicNormalizationAuditUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier candidateRoute frontierRoute publicRoute publicPkg
  obtain ⟨rUnary, cUnary, sUnary, aUnary, _nUnary, _fUnary, _hUnary, _tUnary,
    _pUnary, _lUnary, _localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit,
    _confluenceAuditLedger, _transportReplaySame, _provenancePkg, _localNamePkg⟩ := carrier
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed rUnary cUnary candidateRoute
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateUnary sUnary frontierRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed frontierUnary aUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row ∧
        PkgSig bundle row pkg) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary, publicPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row ∧
            PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row R ∨ hsame row C ∨ hsame row S ∨ hsame row A ∨
              hsame row N ∨ hsame row candidateRead ∨ hsame row frontierRead ∨
                hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont R C candidateRead ∧
              Cont candidateRead S frontierRead ∧ Cont frontierRead A publicRead ∧
                PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, candidateRoute, frontierRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, candidateUnary, frontierUnary, publicUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
