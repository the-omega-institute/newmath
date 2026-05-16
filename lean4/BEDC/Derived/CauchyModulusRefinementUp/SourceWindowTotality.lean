import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_source_window_totality [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
            hsame row h)
        (fun _row : BHist =>
          Cont m0 m1 u ∧ Cont u v t ∧ Cont t w q ∧ Cont q e h ∧
            PkgSig bundle p pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle p pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have carrierWitness :
      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg :=
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro h (And.intro carrierWitness (hsame_refl h))
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
      intro _row _source
      exact ⟨m0m1u, uvt, twq, qeh, pPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport hUnary (hsame_symm source.right), pPkg⟩
  }

end BEDC.Derived.CauchyModulusRefinementUp
