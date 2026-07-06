import BEDC.Derived.RealClassifierUp

namespace BEDC.Derived.RealClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealClassifierCarrier_public_row_surface [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      PkgSig bundle N pkg ->
        hsame publicRead N ->
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
                  hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                    hsame row C ∨ hsame row E ∨ hsame row H ∨ hsame row K ∨
                      hsame row P ∨ hsame row N ∨ hsame row publicRead)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier namePkg samePublicName
  obtain ⟨_xUnary, _yUnary, _sxUnary, _syUnary, _rxUnary, _ryUnary, _wUnary,
    _dUnary, _cUnary, _eUnary, _hUnary, _kUnary, _pUnary, nUnary, _sealPkg⟩ :=
    carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_transport nUnary (hsame_symm samePublicName)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
              hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                hsame row C ∨ hsame row E ∨ hsame row H ∨ hsame row K ∨
                  hsame row P ∨ hsame row N ∨ hsame row publicRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle N pkg)
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, namePkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.RealClassifierUp
