import BEDC.Derived.ToeplitzLemmaUp.RegularSequenceHandoff

namespace BEDC.Derived.ToeplitzLemmaUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ToeplitzLemmaCesaroConsumerRoute [AskSetup] [PackageSetup]
    {A W R D T E H C P N cesaroRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ToeplitzLemmaCarrier A W R D T E H C P N bundle pkg ->
      Cont T E cesaroRead ->
        PkgSig bundle cesaroRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row cesaroRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row A ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row T ∨
                  hsame row E ∨ hsame row cesaroRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont T E cesaroRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle cesaroRead pkg)
              hsame ∧ UnaryHistory cesaroRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier cesaroRoute cesaroPkg
  obtain ⟨_aUnary, _wUnary, _rUnary, _dUnary, tUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, provenancePkg, _namePkg⟩ := carrier
  have cesaroUnary : UnaryHistory cesaroRead :=
    unary_cont_closed tUnary eUnary cesaroRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row cesaroRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row T ∨
              hsame row E ∨ hsame row cesaroRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T E cesaroRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle cesaroRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro cesaroRead ⟨hsame_refl cesaroRead, cesaroUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, cesaroRoute, provenancePkg, cesaroPkg⟩
  }
  exact ⟨cert, cesaroUnary⟩

end BEDC.Derived.ToeplitzLemmaUp
