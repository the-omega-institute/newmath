import BEDC.Derived.RealInverseUp

namespace BEDC.Derived.RealInverseUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealInverseGuardedProductUniqueness [AskSetup] [PackageSetup]
    {x a p w r s h c l n a' p' w' r' h' c' l' n' productRead productRead'
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealInverseCarrier x a p w r s h c l n bundle pkg →
      RealInverseCarrier x a' p' w' r' s h' c' l' n' bundle pkg →
        hsame a a' →
          hsame p p' →
            Cont p r productRead →
              Cont p' r' productRead' →
                hsame productRead productRead' →
                  Cont productRead s sealRead →
                    PkgSig bundle sealRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row x ∨ hsame row a ∨ hsame row a' ∨
                              hsame row p ∨ hsame row p' ∨ hsame row productRead ∨
                                hsame row productRead' ∨ hsame row sealRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle sealRead pkg ∧
                              hsame row sealRead)
                          hsame ∧
                        UnaryHistory productRead ∧ UnaryHistory productRead' ∧
                          UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier carrier' _sameApart _sameProductRoute productRoute productRoute' sameProduct
    sealRoute sealPkg
  obtain ⟨_xUnary, _aUnary, pUnary, _wUnary, rUnary, sUnary, _hUnary, _cUnary,
    _lUnary, _nUnary, _apartRoute, _carrierProductRoute, _localRoute, _ledgerPkg,
      _namePkg⟩ := carrier
  obtain ⟨_xUnary', _aUnary', pUnary', _wUnary', rUnary', _sUnary', _hUnary',
    _cUnary', _lUnary', _nUnary', _apartRoute', _carrierProductRoute', _localRoute',
      _ledgerPkg', _namePkg'⟩ := carrier'
  have productUnary : UnaryHistory productRead :=
    unary_cont_closed pUnary rUnary productRoute
  have _productUnary'FromRoute : UnaryHistory productRead' :=
    unary_cont_closed pUnary' rUnary' productRoute'
  have productUnary' : UnaryHistory productRead' :=
    unary_transport productUnary sameProduct
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed productUnary sUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row x ∨ hsame row a ∨ hsame row a' ∨ hsame row p ∨ hsame row p' ∨
              hsame row productRead ∨ hsame row productRead' ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle sealRead pkg ∧ hsame row sealRead)
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
        source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealPkg, source.left⟩
  }
  exact ⟨cert, productUnary, productUnary', sealUnary⟩

end BEDC.Derived.RealInverseUp
