import BEDC.Derived.RealClassifierUp

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealClassifierTailReplacementStability [AskSetup] [PackageSetup]
    {X Y SX SY RX RY RX' RY' W D C E H K P N leftTail rightTail
      replacementRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      UnaryHistory RX' ->
        UnaryHistory RY' ->
          Cont RX RX' leftTail ->
            Cont RY RY' rightTail ->
              Cont leftTail rightTail replacementRead ->
                PkgSig bundle replacementRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row replacementRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row RX ∨ hsame row RY ∨ hsame row RX' ∨
                          hsame row RY' ∨ hsame row W ∨ hsame row D ∨ hsame row C ∨
                            hsame row E ∨ hsame row replacementRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont RX RX' leftTail ∧
                          Cont RY RY' rightTail ∧ Cont leftTail rightTail replacementRead ∧
                            PkgSig bundle replacementRead pkg)
                      hsame ∧
                    UnaryHistory leftTail ∧ UnaryHistory rightTail ∧
                      UnaryHistory replacementRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier rxPrimeUnary ryPrimeUnary leftRoute rightRoute replacementRoute replacementPkg
  obtain ⟨_xUnary, _yUnary, _sxUnary, _syUnary, rxUnary, ryUnary, _wUnary,
    _dUnary, _cUnary, _eUnary, _hUnary, _kUnary, _pUnary, _nUnary, _sealPkg⟩ :=
    carrier
  have leftTailUnary : UnaryHistory leftTail :=
    unary_cont_closed rxUnary rxPrimeUnary leftRoute
  have rightTailUnary : UnaryHistory rightTail :=
    unary_cont_closed ryUnary ryPrimeUnary rightRoute
  have replacementUnary : UnaryHistory replacementRead :=
    unary_cont_closed leftTailUnary rightTailUnary replacementRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replacementRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row RX ∨ hsame row RY ∨ hsame row RX' ∨ hsame row RY' ∨
              hsame row W ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
                hsame row replacementRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont RX RX' leftTail ∧ Cont RY RY' rightTail ∧
              Cont leftTail rightTail replacementRead ∧ PkgSig bundle replacementRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replacementRead ⟨hsame_refl replacementRead, replacementUnary⟩
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
      exact ⟨source.right, leftRoute, rightRoute, replacementRoute, replacementPkg⟩
  }
  exact ⟨cert, leftTailUnary, rightTailUnary, replacementUnary⟩

end BEDC.Derived
