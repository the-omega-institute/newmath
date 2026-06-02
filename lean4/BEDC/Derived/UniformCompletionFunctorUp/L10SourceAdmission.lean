import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorL10SourceAdmission [AskSetup] [PackageSetup]
    {U F E R W D S H C P N sourceRead windowRead regseqRead dyadicRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont U F sourceRead ->
        Cont sourceRead W windowRead ->
          Cont windowRead R regseqRead ->
            Cont regseqRead D dyadicRead ->
              Cont dyadicRead S sealRead ->
                PkgSig bundle sealRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row U ∨ hsame row F ∨ hsame row R ∨ hsame row W ∨
                          hsame row D ∨ hsame row S ∨ hsame row sourceRead ∨
                            hsame row windowRead ∨ hsame row regseqRead ∨
                              hsame row dyadicRead ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont U F sourceRead ∧
                          Cont sourceRead W windowRead ∧ Cont windowRead R regseqRead ∧
                            Cont regseqRead D dyadicRead ∧ Cont dyadicRead S sealRead ∧
                              PkgSig bundle sealRead pkg)
                      hsame ∧
                    UnaryHistory sourceRead ∧ UnaryHistory windowRead ∧
                      UnaryHistory regseqRead ∧ UnaryHistory dyadicRead ∧
                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier sourceRoute windowRoute regseqRoute dyadicRoute sealRoute sealPkg
  obtain ⟨uUnary, fUnary, _eUnary, rUnary, wUnary, dUnary, sUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _ufe, _erw, _wds, _pkgP, _pkgN⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed uUnary fUnary sourceRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary wUnary windowRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed windowUnary rUnary regseqRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed regseqUnary dUnary dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary sUnary sealRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row R ∨ hsame row W ∨
              hsame row D ∨ hsame row S ∨ hsame row sourceRead ∨
                hsame row windowRead ∨ hsame row regseqRead ∨
                  hsame row dyadicRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U F sourceRead ∧ Cont sourceRead W windowRead ∧
              Cont windowRead R regseqRead ∧ Cont regseqRead D dyadicRead ∧
                Cont dyadicRead S sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, windowRoute, regseqRoute, dyadicRoute, sealRoute,
          sealPkg⟩
  }
  exact ⟨cert, sourceUnary, windowUnary, regseqUnary, dyadicUnary, sealUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
