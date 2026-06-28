import BEDC.Derived.RealClassifierUp

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealClassifierDyadicSourceEmbeddingFaithfulness [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N X' Y' SX' SY' RX' RY' W' C' E' H' K'
      P' N' sourceRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg →
      RealClassifierCarrier X' Y' SX' SY' RX' RY' W' D C' E' H' K' P' N'
          bundle pkg →
        Cont D W sourceRead →
          Cont sourceRead C publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row D ∨ hsame row W ∨ hsame row sourceRead ∨
                      hsame row C ∨ hsame row C' ∨ hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont D W sourceRead ∧
                      Cont sourceRead C publicRead ∧ PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro leftCarrier rightCarrier sourceRoute publicRoute publicPkg
  obtain ⟨_xUnary, _yUnary, _sxUnary, _syUnary, _rxUnary, _ryUnary, wUnary,
    dUnary, cUnary, _eUnary, _hUnary, _kUnary, _pUnary, _nUnary, _sealPkg⟩ :=
    leftCarrier
  obtain ⟨_x'Unary, _y'Unary, _sx'Unary, _sy'Unary, _rx'Unary, _ry'Unary,
    _w'Unary, _d'Unary, _c'Unary, _e'Unary, _h'Unary, _k'Unary, _p'Unary,
    _n'Unary, _seal'Pkg⟩ := rightCarrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed dUnary wUnary sourceRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sourceUnary cUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row sourceRead ∨ hsame row C ∨
              hsame row C' ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W sourceRead ∧ Cont sourceRead C publicRead ∧
              PkgSig bundle publicRead pkg)
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, sourceUnary, publicUnary⟩

end BEDC.Derived
