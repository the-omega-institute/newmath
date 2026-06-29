import BEDC.Derived.RealClassifierUp

namespace BEDC.Derived.RealClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealClassifierCarrier_finite_window_exactness_target [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N windowRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg →
      Cont W D windowRead →
        Cont windowRead E classifierRead →
          PkgSig bundle classifierRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row W ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
                    hsame row RX ∨ hsame row RY ∨ hsame row classifierRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont W D windowRead ∧
                    Cont windowRead E classifierRead ∧ PkgSig bundle classifierRead pkg)
                hsame ∧ UnaryHistory windowRead ∧ UnaryHistory classifierRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute classifierRoute classifierPkg
  obtain ⟨_xUnary, _yUnary, _sxUnary, _syUnary, _rxUnary, _ryUnary, wUnary,
    dUnary, _cUnary, eUnary, _hUnary, _kUnary, _pUnary, _nUnary, _sealPkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary dUnary windowRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed windowUnary eUnary classifierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
              hsame row RX ∨ hsame row RY ∨ hsame row classifierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D windowRead ∧ Cont windowRead E classifierRead ∧
              PkgSig bundle classifierRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifierRead
        ⟨hsame_refl classifierRead, classifierUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, classifierRoute, classifierPkg⟩
  }
  exact ⟨cert, windowUnary, classifierUnary⟩

end BEDC.Derived.RealClassifierUp
