import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_completion_route_pullback_exactness
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n rootFront selected readback sealRead publicRead
      completion : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont m0 u rootFront ->
        Cont t w selected ->
          Cont selected q readback ->
            Cont readback e sealRead ->
              Cont sealRead h publicRead ->
                Cont publicRead c completion ->
                  PkgSig bundle completion pkg ->
                    SemanticNameCert
                      (fun row : BHist =>
                        CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n
                            bundle pkg ∧
                          hsame row completion)
                      (fun row : BHist =>
                        Cont m0 u rootFront ∧ Cont t w selected ∧
                          Cont selected q readback ∧ Cont readback e sealRead ∧
                            Cont sealRead h publicRead ∧ Cont publicRead c row ∧
                              PkgSig bundle completion pkg)
                      (fun row : BHist =>
                        UnaryHistory rootFront ∧ UnaryHistory row ∧
                          PkgSig bundle completion pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier m0uRoot twSelected selectedQReadback readbackESeal sealHPublic
    publicCCompletion completionPkg
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
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary hUnary sealHPublic
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed publicUnary cUnary publicCCompletion
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
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨m0uRoot, twSelected, selectedQReadback, readbackESeal, sealHPublic,
          cont_result_hsame_transport publicCCompletion (hsame_symm source.right),
          completionPkg⟩
    ledger_sound := by
      intro row source
      exact
        ⟨rootUnary, unary_transport completionUnary (hsame_symm source.right),
          completionPkg⟩
  }

end BEDC.Derived.CauchyModulusRefinementUp
