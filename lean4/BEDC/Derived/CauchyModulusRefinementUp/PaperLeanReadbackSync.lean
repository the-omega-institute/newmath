import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_paper_lean_readback_sync [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont h c readback ->
        PkgSig bundle readback pkg ->
          SemanticNameCert
            (fun row : BHist =>
              CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
                hsame row readback)
            (fun _row : BHist =>
              Cont m0 m1 u ∧ Cont u v t ∧ Cont t w q ∧ Cont q e h ∧
                Cont h c readback)
            (fun row : BHist =>
              UnaryHistory row ∧ PkgSig bundle p pkg ∧ PkgSig bundle readback pkg)
            hsame ∧
            UnaryHistory readback ∧ PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier readbackRoute readbackPkg
  obtain ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
    cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩ := carrier
  have carrierWitness :
      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg :=
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed hUnary cUnary readbackRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro readback (And.intro carrierWitness (hsame_refl readback))
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
        exact ⟨m0m1u, uvt, twq, qeh, readbackRoute⟩
      ledger_sound := by
        intro _row source
        exact
          ⟨unary_transport readbackUnary (hsame_symm source.right), pPkg, readbackPkg⟩
    }
  · exact ⟨readbackUnary, readbackPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
