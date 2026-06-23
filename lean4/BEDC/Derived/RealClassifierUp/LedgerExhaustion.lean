import BEDC.Derived.RealClassifierUp

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealClassifierLedgerExhaustion [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N structuralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg →
      Cont H K structuralRead →
        PkgSig bundle structuralRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row structuralRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
                  hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                    hsame row C ∨ hsame row E ∨ hsame row H ∨ hsame row K ∨
                      hsame row P ∨ hsame row N ∨ hsame row structuralRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont H K structuralRead ∧
                  PkgSig bundle structuralRead pkg)
              hsame ∧
            UnaryHistory structuralRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier structuralRoute structuralPkg
  obtain ⟨_xUnary, _yUnary, _sxUnary, _syUnary, _rxUnary, _ryUnary, _wUnary,
    _dUnary, _cUnary, _eUnary, hUnary, kUnary, _pUnary, _nUnary, _sealPkg⟩ :=
    carrier
  have structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed hUnary kUnary structuralRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row structuralRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
              hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                hsame row C ∨ hsame row E ∨ hsame row H ∨ hsame row K ∨
                  hsame row P ∨ hsame row N ∨ hsame row structuralRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont H K structuralRead ∧ PkgSig bundle structuralRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro structuralRead
        ⟨hsame_refl structuralRead, structuralUnary⟩
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
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, structuralRoute, structuralPkg⟩
  }
  exact ⟨cert, structuralUnary⟩

end BEDC.Derived
