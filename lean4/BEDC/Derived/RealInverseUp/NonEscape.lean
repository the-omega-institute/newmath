import BEDC.Derived.RealInverseUp

namespace BEDC.Derived.RealInverseUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealInverseNonEscape [AskSetup] [PackageSetup]
    {x a p w r s h c l n reciprocalWindow productRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealInverseCarrier x a p w r s h c l n bundle pkg →
      Cont a w reciprocalWindow →
        Cont p r productRead →
          Cont productRead s sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row reciprocalWindow ∨ hsame row productRead ∨
                      hsame row sealRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row x ∨ hsame row a ∨ hsame row p ∨ hsame row w ∨
                      hsame row r ∨ hsame row s ∨ hsame row reciprocalWindow ∨
                        hsame row productRead ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont a w reciprocalWindow ∧
                      Cont p r productRead ∧ Cont productRead s sealRead ∧
                        PkgSig bundle sealRead pkg)
                  hsame ∧ UnaryHistory reciprocalWindow ∧ UnaryHistory productRead ∧
                UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier reciprocalRoute productRoute sealRoute sealPkg
  obtain ⟨_xUnary, aUnary, pUnary, wUnary, rUnary, sUnary, _hUnary, _cUnary,
    _lUnary, _nUnary, _apartRoute, _carrierProductRoute, _localRoute, _ledgerPkg,
      _namePkg⟩ := carrier
  have reciprocalUnary : UnaryHistory reciprocalWindow :=
    unary_cont_closed aUnary wUnary reciprocalRoute
  have productUnary : UnaryHistory productRead :=
    unary_cont_closed pUnary rUnary productRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed productUnary sUnary sealRoute
  have sourceSeal :
      (fun row : BHist =>
        (hsame row reciprocalWindow ∨ hsame row productRead ∨ hsame row sealRead) ∧
          UnaryHistory row) sealRead := by
    exact ⟨Or.inr (Or.inr (hsame_refl sealRead)), sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row reciprocalWindow ∨ hsame row productRead ∨ hsame row sealRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row x ∨ hsame row a ∨ hsame row p ∨ hsame row w ∨
              hsame row r ∨ hsame row s ∨ hsame row reciprocalWindow ∨
                hsame row productRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont a w reciprocalWindow ∧ Cont p r productRead ∧
              Cont productRead s sealRead ∧ PkgSig bundle sealRead pkg)
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
        constructor
        · cases source.left with
          | inl sameReciprocal =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameReciprocal)
          | inr rest =>
              cases rest with
              | inl sameProduct =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameProduct))
              | inr sameSeal =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameSeal))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameReciprocal =>
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inl sameReciprocal
      | inr rest =>
          cases rest with
          | inl sameProduct =>
              exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                Or.inr <| Or.inl sameProduct
          | inr sameSeal =>
              exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                Or.inr <| Or.inr sameSeal
    ledger_sound := by
      intro _row source
      exact ⟨source.right, reciprocalRoute, productRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, reciprocalUnary, productUnary, sealUnary⟩

end BEDC.Derived.RealInverseUp
