import BEDC.Derived.RealZeroUp

namespace BEDC.Derived.RealZeroUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealZeroCarrier_ledger_nonescape [AskSetup] [PackageSetup]
    {q S Z0 D R H C P N ledgerRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealZeroCarrier q S Z0 D R H C P N ->
      Cont Z0 D ledgerRead ->
        Cont ledgerRead N namedRead ->
          PkgSig bundle namedRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row q ∨ hsame row S ∨ hsame row Z0 ∨ hsame row D ∨
                    hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N ∨ hsame row ledgerRead ∨ hsame row namedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont Z0 D ledgerRead ∧
                    Cont ledgerRead N namedRead ∧ PkgSig bundle namedRead pkg)
                hsame ∧
              hsame ledgerRead R ∧ UnaryHistory ledgerRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: RealZeroCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier ledgerRoute namedRoute namedPkg
  obtain ⟨_qUnary, _sUnary, z0Unary, dUnary, _rUnary, _hUnary, _cUnary, _pUnary,
    nUnary, _zeroRoute, terminalRoute, _sameH, _sameC, _sameP, _sameN,
    _terminalCert⟩ := carrier
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed z0Unary dUnary ledgerRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed ledgerUnary nUnary namedRoute
  have sameLedger : hsame ledgerRead R :=
    cont_respects_hsame (hsame_refl Z0) (hsame_refl D) ledgerRoute terminalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row S ∨ hsame row Z0 ∨ hsame row D ∨
              hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row ledgerRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z0 D ledgerRead ∧ Cont ledgerRead N namedRead ∧
              PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, ledgerRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, sameLedger, ledgerUnary, namedUnary⟩

end BEDC.Derived.RealZeroUp
