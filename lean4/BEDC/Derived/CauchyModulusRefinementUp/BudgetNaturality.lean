import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_budget_naturality [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n m0' m1' u' v' t' w' q' e' h' c' p' n' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      CauchyModulusRefinementCarrier m0' m1' u' v' t' w' q' e' h' c' p' n'
          bundle pkg ->
        hsame m0 m0' ->
          hsame m1 m1' ->
            hsame v v' ->
              hsame w w' ->
                hsame e e' ->
                  hsame u u' ∧ hsame t t' ∧ hsame q q' ∧ hsame h h' ∧
                    UnaryHistory u' ∧ UnaryHistory t' ∧ UnaryHistory q' ∧
                      UnaryHistory h' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier carrier' sameM0 sameM1 sameV sameW sameE
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, source, selector, window, sealRow, _pkgSig,
      _sameSeal⟩
  rcases carrier' with
    ⟨_m0Unary', _m1Unary', uUnary', _vUnary', tUnary', _wUnary', qUnary', _eUnary',
      hUnary', _cUnary', _pUnary', _nUnary', source', selector', window', sealRow',
      _pkgSig', _sameSeal'⟩
  have sameU : hsame u u' :=
    cont_respects_hsame sameM0 sameM1 source source'
  have sameT : hsame t t' :=
    cont_respects_hsame sameU sameV selector selector'
  have sameQ : hsame q q' :=
    cont_respects_hsame sameT sameW window window'
  have sameH : hsame h h' :=
    cont_respects_hsame sameQ sameE sealRow sealRow'
  exact ⟨sameU, sameT, sameQ, sameH, uUnary', tUnary', qUnary', hUnary'⟩

end BEDC.Derived.CauchyModulusRefinementUp
