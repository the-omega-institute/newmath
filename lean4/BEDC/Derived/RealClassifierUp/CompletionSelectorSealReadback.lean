import BEDC.Derived.RealClassifierUp

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealClassifierCompletionSelectorSealReadback [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N selectorRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      Cont W D classifierRead ->
        Cont classifierRead N selectorRead ->
          PkgSig bundle selectorRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row X ∨ hsame row Y ∨ hsame row RX ∨ hsame row RY ∨
                    hsame row W ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
                      hsame row N ∨ hsame row selectorRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont W D classifierRead ∧
                    Cont classifierRead N selectorRead ∧ PkgSig bundle selectorRead pkg)
                hsame ∧ UnaryHistory classifierRead ∧ UnaryHistory selectorRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier classifierRoute selectorRoute selectorPkg
  obtain ⟨_xUnary, _yUnary, _sxUnary, _syUnary, _rxUnary, _ryUnary, wUnary,
    dUnary, _cUnary, _eUnary, _hUnary, _kUnary, _pUnary, nUnary, _sealPkg⟩ :=
    carrier
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed wUnary dUnary classifierRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed classifierUnary nUnary selectorRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row RX ∨ hsame row RY ∨
              hsame row W ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
                hsame row N ∨ hsame row selectorRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D classifierRead ∧
              Cont classifierRead N selectorRead ∧ PkgSig bundle selectorRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro selectorRead
        ⟨hsame_refl selectorRead, selectorUnary⟩
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
        Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, classifierRoute, selectorRoute, selectorPkg⟩
  }
  exact ⟨cert, classifierUnary, selectorUnary⟩

end BEDC.Derived
