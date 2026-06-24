import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealInverseUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealInverseCarrier [AskSetup] [PackageSetup]
    (x a p w r s h c l n : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory x ∧ UnaryHistory a ∧ UnaryHistory p ∧ UnaryHistory w ∧ UnaryHistory r ∧
    UnaryHistory s ∧ UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory l ∧ UnaryHistory n ∧
      Cont a w r ∧ Cont p r s ∧ Cont c l n ∧ PkgSig bundle l pkg ∧ PkgSig bundle n pkg

theorem RealInverseNameCertObligations [AskSetup] [PackageSetup]
    {x a p w r s h c l n : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealInverseCarrier x a p w r s h c l n bundle pkg →
      SemanticNameCert
        (fun row : BHist => RealInverseCarrier x a p w r s h c l n bundle pkg ∧ hsame row n)
        (fun row : BHist => RealInverseCarrier x a p w r s h c l n bundle pkg ∧ hsame row n)
        (fun row : BHist => RealInverseCarrier x a p w r s h c l n bundle pkg ∧ hsame row n)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro n ⟨carrier, hsame_refl n⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem RealInverseProductSealHandoff [AskSetup] [PackageSetup]
    {x a p w r s h c l n productRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealInverseCarrier x a p w r s h c l n bundle pkg →
      Cont p r productRead →
        Cont productRead s sealRead →
          PkgSig bundle sealRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row x ∨ hsame row a ∨ hsame row p ∨ hsame row w ∨
                    hsame row r ∨ hsame row s ∨ hsame row productRead ∨
                      hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont p r productRead ∧
                    Cont productRead s sealRead ∧ PkgSig bundle sealRead pkg)
                hsame ∧ UnaryHistory productRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier productRoute sealRoute sealPkg
  obtain ⟨_xUnary, _aUnary, pUnary, _wUnary, rUnary, sUnary, _hUnary, _cUnary,
    _lUnary, _nUnary, _apartRoute, _carrierProductRoute, _localRoute, _ledgerPkg,
      _namePkg⟩ := carrier
  have productUnary : UnaryHistory productRead :=
    unary_cont_closed pUnary rUnary productRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed productUnary sUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row x ∨ hsame row a ∨ hsame row p ∨ hsame row w ∨
              hsame row r ∨ hsame row s ∨ hsame row productRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont p r productRead ∧
              Cont productRead s sealRead ∧ PkgSig bundle sealRead pkg)
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, productRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, productUnary, sealUnary⟩

theorem RealInverseApartnessProductScopedFactorization [AskSetup] [PackageSetup]
    {x a p w r s h c l n reciprocalWindow productRead sealRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealInverseCarrier x a p w r s h c l n bundle pkg →
      Cont a w reciprocalWindow →
        Cont p r productRead →
          Cont productRead s sealRead →
            Cont sealRead n scopedRead →
              PkgSig bundle scopedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row x ∨ hsame row a ∨ hsame row p ∨ hsame row w ∨
                        hsame row r ∨ hsame row s ∨ hsame row n ∨
                          hsame row reciprocalWindow ∨ hsame row productRead ∨
                            hsame row sealRead ∨ hsame row scopedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont a w reciprocalWindow ∧
                        Cont p r productRead ∧ Cont productRead s sealRead ∧
                          Cont sealRead n scopedRead ∧ PkgSig bundle scopedRead pkg)
                    hsame ∧ UnaryHistory reciprocalWindow ∧ UnaryHistory productRead ∧
                  UnaryHistory sealRead ∧ UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier reciprocalRoute productRoute sealRoute scopedRoute scopedPkg
  obtain ⟨_xUnary, aUnary, pUnary, wUnary, rUnary, sUnary, _hUnary, _cUnary,
    _lUnary, nUnary, _apartRoute, _carrierProductRoute, _localRoute, _ledgerPkg,
      _namePkg⟩ := carrier
  have reciprocalUnary : UnaryHistory reciprocalWindow :=
    unary_cont_closed aUnary wUnary reciprocalRoute
  have productUnary : UnaryHistory productRead :=
    unary_cont_closed pUnary rUnary productRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed productUnary sUnary sealRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed sealUnary nUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row x ∨ hsame row a ∨ hsame row p ∨ hsame row w ∨
              hsame row r ∨ hsame row s ∨ hsame row n ∨
                hsame row reciprocalWindow ∨ hsame row productRead ∨
                  hsame row sealRead ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont a w reciprocalWindow ∧ Cont p r productRead ∧
              Cont productRead s sealRead ∧ Cont sealRead n scopedRead ∧
                PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead
        ⟨hsame_refl scopedRead, scopedUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, reciprocalRoute, productRoute, sealRoute, scopedRoute, scopedPkg⟩
  }
  exact ⟨cert, reciprocalUnary, productUnary, sealUnary, scopedUnary⟩

end BEDC.Derived.RealInverseUp
