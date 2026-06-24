import BEDC.Derived.RealClassifierUp

namespace BEDC.Derived.RealClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealClassifierRegularRealTailEquivalenceReadback [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N tailRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      Cont RX RY tailRead ->
        Cont tailRead E publicRead ->
          PkgSig bundle publicRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                    hsame row C ∨ hsame row E ∨ hsame row tailRead ∨
                      hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont RX RY tailRead ∧
                    Cont tailRead E publicRead ∧ PkgSig bundle publicRead pkg)
                hsame ∧
              UnaryHistory tailRead ∧ UnaryHistory publicRead ∧ PkgSig bundle E pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro carrier tailRoute publicRoute publicPkg
  obtain
    ⟨_xUnary, _yUnary, _sxUnary, _syUnary, rxUnary, ryUnary, _wUnary, _dUnary,
      _cUnary, eUnary, _hUnary, _kUnary, _pUnary, _nUnary, sealPkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed rxUnary ryUnary tailRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed tailUnary eUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
              hsame row C ∨ hsame row E ∨ hsame row tailRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont RX RY tailRead ∧
              Cont tailRead E publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead
        ⟨hsame_refl publicRead, publicUnary⟩
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
      exact ⟨source.right, tailRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, tailUnary, publicUnary, sealPkg⟩

end BEDC.Derived.RealClassifierUp
