import BEDC.Derived.MetaCICOpenProblemLedgerUp

namespace BEDC.Derived.MetaCICOpenProblemLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICOpenProblemLedger_nonescape [AskSetup] [PackageSetup]
    {S C N U D E B H R P Q consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICOpenProblemLedgerCarrier S C N U D E B H R P Q bundle pkg →
      Cont R P consumerRead →
        PkgSig bundle consumerRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row C ∨ hsame row N ∨ hsame row U ∨
                  hsame row D ∨ hsame row E ∨ hsame row B ∨ hsame row consumerRead)
              (fun row : BHist => hsame row consumerRead ∧ PkgSig bundle consumerRead pkg)
              hsame ∧
            UnaryHistory consumerRead ∧ Cont R P consumerRead ∧
              PkgSig bundle Q pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier consumerRoute consumerPkg
  obtain ⟨_sUnary, _cUnary, _nUnary, _uUnary, _dUnary, _eUnary, _bUnary, _hUnary,
    rUnary, pUnary, _qUnary, _hSelf, _headerRoute, _localRoute, localPkg⟩ :=
    carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed rUnary pUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row C ∨ hsame row N ∨ hsame row U ∨ hsame row D ∨
              hsame row E ∨ hsame row B ∨ hsame row consumerRead)
          (fun row : BHist => hsame row consumerRead ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerPkg⟩
  }
  exact ⟨cert, consumerUnary, consumerRoute, localPkg.right, consumerPkg⟩

end BEDC.Derived.MetaCICOpenProblemLedgerUp
