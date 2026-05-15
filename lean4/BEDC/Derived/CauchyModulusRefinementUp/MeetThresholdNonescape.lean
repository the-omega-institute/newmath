import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_meet_threshold_nonescape [AskSetup] [PackageSetup]
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
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier tWSelected selectedQReadback readbackESeal sealPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackESeal
  have carrierPacket :
      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg :=
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead (And.intro carrierPacket (hsame_refl sealRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨m0m1u, uvt, tWSelected, selectedQReadback,
          cont_result_hsame_transport readbackESeal (hsame_symm source.right), sealPkg⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport sealUnary (hsame_symm source.right), sealPkg⟩
  }

end BEDC.Derived.CauchyModulusRefinementUp
