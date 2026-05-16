import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_source_window_real_seal_pullback
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n rootFront selected readback sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont m0 u rootFront →
        Cont t w selected →
          Cont selected q readback →
            Cont readback e sealRead →
              Cont sealRead h publicRead →
                PkgSig bundle publicRead pkg →
                  SemanticNameCert
                    (fun row : BHist =>
                      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n
                          bundle pkg ∧
                        hsame row publicRead)
                    (fun row : BHist =>
                      Cont m0 u rootFront ∧ Cont t w selected ∧
                        Cont selected q readback ∧ Cont readback e sealRead ∧
                          Cont sealRead h row ∧ PkgSig bundle publicRead pkg)
                    (fun row : BHist =>
                      UnaryHistory rootFront ∧ UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier m0uRoot twSelected selectedQReadback readbackESeal sealHPublic publicPkg
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
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead
          (And.intro
            ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
              cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
            (hsame_refl publicRead))
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
        ⟨m0uRoot, twSelected, selectedQReadback, readbackESeal,
          cont_result_hsame_transport sealHPublic (hsame_symm source.right), publicPkg⟩
    ledger_sound := by
      intro row source
      exact
        ⟨rootUnary, unary_transport publicUnary (hsame_symm source.right), publicPkg⟩
  }

end BEDC.Derived.CauchyModulusRefinementUp
