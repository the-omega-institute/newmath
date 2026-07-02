import BEDC.Derived.RealClassifierUp

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealClassifierRegSeqRatWindowExhaustion [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N regRead windowRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      Cont SX RX regRead ->
        Cont regRead W windowRead ->
          Cont windowRead D publicRead ->
            PkgSig bundle publicRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row SX ∨ hsame row RX ∨ hsame row W ∨ hsame row D ∨
                      hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont SX RX regRead ∧
                      Cont regRead W windowRead ∧ Cont windowRead D publicRead ∧
                        PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory regRead ∧ UnaryHistory windowRead ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier regRoute windowRoute publicRoute publicPkg
  obtain ⟨_xUnary, _yUnary, sxUnary, _syUnary, rxUnary, _ryUnary, wUnary,
    dUnary, _cUnary, _eUnary, _hUnary, _kUnary, _pUnary, _nUnary, _sealPkg⟩ :=
    carrier
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed sxUnary rxUnary regRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed regUnary wUnary windowRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed windowUnary dUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row SX ∨ hsame row RX ∨ hsame row W ∨ hsame row D ∨
              hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont SX RX regRead ∧ Cont regRead W windowRead ∧
              Cont windowRead D publicRead ∧ PkgSig bundle publicRead pkg)
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regRoute, windowRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, regUnary, windowUnary, publicUnary⟩

end BEDC.Derived
