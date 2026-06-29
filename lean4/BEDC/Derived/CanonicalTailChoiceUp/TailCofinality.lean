import BEDC.Derived.CanonicalTailChoiceUp.Nonescape

namespace BEDC.Derived.CanonicalTailChoiceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CanonicalTailChoiceCarrier_tail_cofinality [AskSetup] [PackageSetup]
    {M E I T S R H C0 P N cofinalWindow lateRequest tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CanonicalTailChoiceCarrier M E I T S R H C0 P N bundle pkg →
      Cont I T cofinalWindow →
        Cont cofinalWindow H lateRequest →
          Cont lateRequest C0 tailRead →
            PkgSig bundle tailRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row E ∨ hsame row I ∨ hsame row T ∨
                      hsame row S ∨ hsame row R ∨ hsame row H ∨ hsame row C0 ∨
                        hsame row cofinalWindow ∨ hsame row lateRequest ∨
                          hsame row tailRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont I T cofinalWindow ∧
                      Cont cofinalWindow H lateRequest ∧
                        Cont lateRequest C0 tailRead ∧ PkgSig bundle tailRead pkg)
                  hsame ∧
                UnaryHistory cofinalWindow ∧
                  UnaryHistory lateRequest ∧ UnaryHistory tailRead := by
  -- BEDC touchpoint anchor: CanonicalTailChoiceCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier cofinalRoute lateRoute tailRoute tailPkg
  obtain ⟨_mUnary, _eUnary, iUnary, tUnary, _sUnary, _rUnary, hUnary, c0Unary,
    _pUnary, _nUnary, _pPkg, _nPkg⟩ := carrier
  have cofinalUnary : UnaryHistory cofinalWindow :=
    unary_cont_closed iUnary tUnary cofinalRoute
  have lateUnary : UnaryHistory lateRequest :=
    unary_cont_closed cofinalUnary hUnary lateRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed lateUnary c0Unary tailRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row E ∨ hsame row I ∨ hsame row T ∨ hsame row S ∨
              hsame row R ∨ hsame row H ∨ hsame row C0 ∨ hsame row cofinalWindow ∨
                hsame row lateRequest ∨ hsame row tailRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont I T cofinalWindow ∧
              Cont cofinalWindow H lateRequest ∧ Cont lateRequest C0 tailRead ∧
                PkgSig bundle tailRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro tailRead ⟨hsame_refl tailRead, tailUnary⟩
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
        intro _row _other sameRows sourceData
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceData.left,
            unary_transport sourceData.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceData
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr sourceData.left)))))))))
    ledger_sound := by
      intro _row sourceData
      exact ⟨sourceData.right, cofinalRoute, lateRoute, tailRoute, tailPkg⟩
  }
  exact ⟨cert, cofinalUnary, lateUnary, tailUnary⟩

end BEDC.Derived.CanonicalTailChoiceUp
