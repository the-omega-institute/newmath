import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorWindowFunctoriality [AskSetup] [PackageSetup]
    {U F E R W D S H C P N U2 F2 E2 R2 W2 D2 S2 H2 C2 P2 N2 sourceRead
      windowRead readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      UniformCompletionFunctorCarrier U2 F2 E2 R2 W2 D2 S2 H2 C2 P2 N2 bundle pkg ->
        Cont U U2 sourceRead ->
          Cont W W2 windowRead ->
            Cont R R2 readbackRead ->
              Cont windowRead readbackRead sealRead ->
                PkgSig bundle sealRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row U ∨ hsame row U2 ∨ hsame row W ∨ hsame row W2 ∨
                          hsame row R ∨ hsame row R2 ∨ hsame row sourceRead ∨
                            hsame row windowRead ∨ hsame row readbackRead ∨
                              hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont U U2 sourceRead ∧
                          Cont W W2 windowRead ∧ Cont R R2 readbackRead ∧
                            Cont windowRead readbackRead sealRead ∧
                              PkgSig bundle sealRead pkg)
                      hsame ∧
                    UnaryHistory sourceRead ∧ UnaryHistory windowRead ∧
                      UnaryHistory readbackRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro leftCarrier rightCarrier sourceRoute windowRoute readbackRoute sealRoute sealPkg
  obtain ⟨uUnary, _fUnary, _eUnary, rUnary, wUnary, _dUnary, _sUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _sourceCarrierRoute, _readbackCarrierRoute,
    _sealCarrierRoute, _provenancePkg, _localNamePkg⟩ := leftCarrier
  obtain ⟨u2Unary, _f2Unary, _e2Unary, r2Unary, w2Unary, _d2Unary, _s2Unary, _h2Unary,
    _c2Unary, _p2Unary, _n2Unary, _sourceCarrierRoute2, _readbackCarrierRoute2,
    _sealCarrierRoute2, _provenancePkg2, _localNamePkg2⟩ := rightCarrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed uUnary u2Unary sourceRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary w2Unary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed rUnary r2Unary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary readbackUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row U2 ∨ hsame row W ∨ hsame row W2 ∨
              hsame row R ∨ hsame row R2 ∨ hsame row sourceRead ∨
                hsame row windowRead ∨ hsame row readbackRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U U2 sourceRead ∧
              Cont W W2 windowRead ∧ Cont R R2 readbackRead ∧
                Cont windowRead readbackRead sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, windowRoute, readbackRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, sourceUnary, windowUnary, readbackUnary, sealUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
