import BEDC.Derived.CanonicalTailChoiceUp.ScopedSourceDiscipline

namespace BEDC.Derived.CanonicalTailChoiceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CanonicalTailChoiceCarrier_public_export [AskSetup] [PackageSetup]
    {M E I T S R H C0 P N tailRead sealRead boundaryRead sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CanonicalTailChoiceCarrier M E I T S R H C0 P N bundle pkg →
      Cont I T tailRead →
        Cont tailRead S sealRead →
          Cont sealRead R boundaryRead →
            Cont boundaryRead C0 sourceRead →
              PkgSig bundle sourceRead pkg →
                SemanticNameCert
                  (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row E ∨ hsame row I ∨ hsame row T ∨
                      hsame row S ∨ hsame row R ∨ hsame row H ∨ hsame row C0 ∨
                        hsame row P ∨ hsame row N ∨ hsame row tailRead ∨
                          hsame row sealRead ∨ hsame row boundaryRead ∨
                            hsame row sourceRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont I T tailRead ∧
                      Cont tailRead S sealRead ∧ Cont sealRead R boundaryRead ∧
                        Cont boundaryRead C0 sourceRead ∧
                          PkgSig bundle sourceRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: CanonicalTailChoiceCarrier BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier tailRoute sealRoute boundaryRoute sourceRoute sourcePkg
  obtain ⟨_mUnary, _eUnary, iUnary, tUnary, sUnary, rUnary, _hUnary, c0Unary,
    _pUnary, _nUnary, _pPkg, _nPkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed iUnary tUnary tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sUnary sealRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sealUnary rUnary boundaryRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed boundaryUnary c0Unary sourceRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sourceRead ⟨hsame_refl sourceRead, sourceUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, tailRoute, sealRoute, boundaryRoute, sourceRoute, sourcePkg⟩
  }

end BEDC.Derived.CanonicalTailChoiceUp
