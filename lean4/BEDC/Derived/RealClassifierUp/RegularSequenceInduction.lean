import BEDC.Derived.RealClassifierUp

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealClassifierRegularSequenceInduction [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N firstRead stepRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg →
      Cont W D firstRead →
        Cont firstRead C stepRead →
          PkgSig bundle stepRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row stepRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
                    hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                      hsame row C ∨ hsame row E ∨ hsame row H ∨ hsame row K ∨
                        hsame row P ∨ hsame row N ∨ hsame row firstRead ∨
                          hsame row stepRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont W D firstRead ∧
                    Cont firstRead C stepRead ∧ PkgSig bundle stepRead pkg)
                hsame ∧
              UnaryHistory firstRead ∧ UnaryHistory stepRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier firstRoute stepRoute stepPkg
  obtain ⟨_xUnary, _yUnary, _sxUnary, _syUnary, _rxUnary, _ryUnary, wUnary,
    dUnary, cUnary, _eUnary, _hUnary, _kUnary, _pUnary, _nUnary, _sealPkg⟩ :=
    carrier
  have firstUnary : UnaryHistory firstRead :=
    unary_cont_closed wUnary dUnary firstRoute
  have stepUnary : UnaryHistory stepRead :=
    unary_cont_closed firstUnary cUnary stepRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stepRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
              hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                hsame row C ∨ hsame row E ∨ hsame row H ∨ hsame row K ∨
                  hsame row P ∨ hsame row N ∨ hsame row firstRead ∨
                    hsame row stepRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D firstRead ∧ Cont firstRead C stepRead ∧
              PkgSig bundle stepRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro stepRead
        ⟨hsame_refl stepRead, stepUnary⟩
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
            Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, firstRoute, stepRoute, stepPkg⟩
  }
  exact ⟨cert, firstUnary, stepUnary⟩

end BEDC.Derived
