import BEDC.Derived.RealClassifierUp

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealClassifierCompletionDensityConsumer [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N densityRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      Cont W D classifierRead ->
        Cont classifierRead P densityRead ->
          PkgSig bundle densityRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row densityRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row X ∨ hsame row Y ∨ hsame row RX ∨ hsame row RY ∨
                    hsame row W ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
                      hsame row densityRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont W D classifierRead ∧
                    Cont classifierRead P densityRead ∧ PkgSig bundle densityRead pkg)
                hsame ∧
              UnaryHistory classifierRead ∧ UnaryHistory densityRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier classifierRoute densityRoute densityPkg
  obtain ⟨_xUnary, _yUnary, _sxUnary, _syUnary, _rxUnary, _ryUnary, wUnary,
    dUnary, _cUnary, _eUnary, _hUnary, _kUnary, pUnary, _nUnary, _sealPkg⟩ :=
    carrier
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed wUnary dUnary classifierRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed classifierUnary pUnary densityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row densityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row RX ∨ hsame row RY ∨
              hsame row W ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
                hsame row densityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D classifierRead ∧
              Cont classifierRead P densityRead ∧ PkgSig bundle densityRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro densityRead
        ⟨hsame_refl densityRead, densityUnary⟩
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
        Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, classifierRoute, densityRoute, densityPkg⟩
  }
  exact ⟨cert, classifierUnary, densityUnary⟩

end BEDC.Derived
