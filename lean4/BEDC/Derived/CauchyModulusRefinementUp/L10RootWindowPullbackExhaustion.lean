import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_l10_root_window_pullback_exhaustion
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n rootFront selected readback sealRead support
      completion : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont m0 u rootFront ->
        Cont t w selected ->
          Cont selected q readback ->
            Cont readback e sealRead ->
              Cont sealRead h support ->
                Cont support c completion ->
                  PkgSig bundle completion pkg ->
                    SemanticNameCert
                      (fun row : BHist =>
                        CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n
                            bundle pkg ∧
                          hsame row completion)
                      (fun row : BHist =>
                        Cont m0 u rootFront ∧ Cont t w selected ∧
                          Cont selected q readback ∧ Cont readback e sealRead ∧
                            Cont sealRead h support ∧ Cont support c row ∧
                              PkgSig bundle completion pkg)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle completion pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier m0uRoot twSelected selectedQReadback readbackESeal sealHSupport
    supportCCompletion completionPkg
  obtain ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
    cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩ := carrier
  have rootUnary : UnaryHistory rootFront :=
    unary_cont_closed m0Unary uUnary m0uRoot
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary twSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackESeal
  have supportUnary : UnaryHistory support :=
    unary_cont_closed sealUnary hUnary sealHSupport
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed supportUnary cUnary supportCCompletion
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro completion
          (And.intro
            ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
              cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
            (hsame_refl completion))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨m0uRoot, twSelected, selectedQReadback, readbackESeal, sealHSupport,
          cont_result_hsame_transport supportCCompletion (hsame_symm source.right),
          completionPkg⟩
    ledger_sound := by
      intro _row source
      exact And.intro (unary_transport completionUnary (hsame_symm source.right))
        completionPkg
  }

end BEDC.Derived.CauchyModulusRefinementUp
