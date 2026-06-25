import BEDC.Derived.RealClassifierUp

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealClassifierPublicExportReadback [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N publicRead selectorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      Cont SX RX publicRead ->
        Cont SY RY selectorRead ->
          PkgSig bundle publicRead pkg ->
            PkgSig bundle selectorRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row publicRead ∨ hsame row selectorRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row SX ∨ hsame row SY ∨ hsame row RX ∨ hsame row RY ∨
                      hsame row W ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
                        hsame row H ∨ hsame row K ∨ hsame row P ∨ hsame row N ∨
                          hsame row publicRead ∨ hsame row selectorRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧
                      (PkgSig bundle publicRead pkg ∨ PkgSig bundle selectorRead pkg))
                  hsame ∧
                UnaryHistory publicRead ∧ UnaryHistory selectorRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier publicRoute selectorRoute publicPkg selectorPkg
  obtain ⟨_xUnary, _yUnary, sxUnary, syUnary, rxUnary, ryUnary, _wUnary, _dUnary,
    _cUnary, _eUnary, _hUnary, _kUnary, _pUnary, _nUnary, _sealPkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sxUnary rxUnary publicRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed syUnary ryUnary selectorRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row publicRead ∨ hsame row selectorRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row SX ∨ hsame row SY ∨ hsame row RX ∨ hsame row RY ∨
              hsame row W ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
                hsame row H ∨ hsame row K ∨ hsame row P ∨ hsame row N ∨
                  hsame row publicRead ∨ hsame row selectorRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              (PkgSig bundle publicRead pkg ∨ PkgSig bundle selectorRead pkg))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead
        ⟨Or.inl (hsame_refl publicRead), publicUnary⟩
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
          | inl samePublic =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) samePublic)
          | inr sameSelector =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameSelector)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl samePublic =>
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
              Or.inl samePublic
      | inr sameSelector =>
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
              Or.inr sameSelector
    ledger_sound := by
      intro _row source
      cases source.left with
      | inl _samePublic =>
          exact ⟨source.right, Or.inl publicPkg⟩
      | inr _sameSelector =>
          exact ⟨source.right, Or.inr selectorPkg⟩
  }
  exact ⟨cert, publicUnary, selectorUnary⟩

end BEDC.Derived
