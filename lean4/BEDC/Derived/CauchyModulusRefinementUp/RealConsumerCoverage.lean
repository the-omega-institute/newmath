import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_real_consumer_coverage [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont q e sealRead ->
        PkgSig bundle sealRead pkg ->
          SemanticNameCert
            (fun row : BHist =>
              CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
                hsame row sealRead)
            (fun row : BHist =>
              Cont m0 m1 u ∧ Cont u v t ∧ Cont t w q ∧ Cont q e row ∧
                PkgSig bundle sealRead pkg)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealRead pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame
  intro carrier sealRoute sealPkg
  have carrierWitness := carrier
  obtain ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, qUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, twq, _qeh, _pPkg, _hn⟩ :=
      carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed qUnary eUnary sealRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead (And.intro carrierWitness (hsame_refl sealRead))
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
        ⟨m0m1u, uvt, twq, cont_result_hsame_transport sealRoute
          (hsame_symm source.right), sealPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport sealReadUnary (hsame_symm source.right), sealPkg⟩
  }

end BEDC.Derived.CauchyModulusRefinementUp
