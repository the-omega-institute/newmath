import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_sibling_dependency_lattice
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            PkgSig bundle sealRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n
                    bundle pkg ∧ hsame row sealRead)
                (fun row : BHist =>
                  Cont m0 m1 u ∧ Cont u v t ∧ Cont t w selected ∧
                    Cont selected q readback ∧ Cont readback e row ∧
                      PkgSig bundle sealRead pkg)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier selectedRoute readbackRoute sealRoute sealPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary selectedRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have carrierSource :
      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg :=
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead (And.intro carrierSource (hsame_refl sealRead))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨m0m1u, uvt, selectedRoute, readbackRoute,
          cont_result_hsame_transport sealRoute (hsame_symm source.right), sealPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport sealReadUnary (hsame_symm source.right), sealPkg⟩
  }

end BEDC.Derived.CauchyModulusRefinementUp
