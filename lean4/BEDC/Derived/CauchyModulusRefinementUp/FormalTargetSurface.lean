import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_formal_target_surface [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont h c endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
            (fun row : BHist =>
              CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
                hsame row endpoint)
            (fun row : BHist =>
              Cont m0 m1 u ∧ Cont u v t ∧ Cont t w q ∧ Cont q e h ∧
                Cont h c row ∧ PkgSig bundle p pkg ∧ PkgSig bundle endpoint pkg)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpoint pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier hEndpoint endpointPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed hUnary cUnary hEndpoint
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro
          ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
            cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
          (hsame_refl endpoint))
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
        ⟨m0m1u, uvt, twq, qeh,
          cont_result_hsame_transport hEndpoint (hsame_symm source.right), pPkg,
          endpointPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport endpointUnary (hsame_symm source.right), endpointPkg⟩
  }

end BEDC.Derived.CauchyModulusRefinementUp
