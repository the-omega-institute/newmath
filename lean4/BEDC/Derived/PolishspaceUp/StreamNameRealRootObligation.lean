import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceStreamNameRealRootObligation [AskSetup] [PackageSetup]
    {M K D S R W H C G N streamRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishSpaceCarrier M K D S R W H C G N bundle pkg ->
      Cont S R streamRead ->
        Cont streamRead W realRead ->
          PkgSig bundle realRead pkg ->
            UnaryHistory streamRead ∧ UnaryHistory realRead ∧
              SemanticNameCert
                (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S ∨ hsame row R ∨ hsame row W ∨
                    hsame row streamRead ∨ hsame row realRead)
                (fun row : BHist =>
                  hsame row realRead ∧ PkgSig bundle G pkg ∧
                    PkgSig bundle realRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: PolishSpaceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier streamRoute realRoute realPkg
  obtain ⟨_mUnary, _kUnary, _dUnary, sUnary, rUnary, wUnary, _hUnary, _cUnary,
    _gUnary, _nUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, provenancePkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed sUnary rUnary streamRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed streamUnary wUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row W ∨
              hsame row streamRead ∨ hsame row realRead)
          (fun row : BHist =>
            hsame row realRead ∧ PkgSig bundle G pkg ∧ PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, realPkg⟩
  }
  exact ⟨streamUnary, realUnary, cert⟩

end BEDC.Derived.PolishSpaceUp
