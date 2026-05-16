import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementTerminalSpineChoiceRefusal [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n t' w' q' e' h' publicRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      hsame t t' ->
        hsame w w' ->
          hsame e e' ->
            Cont t' w' q' ->
              Cont q' e' h' ->
                Cont h' c publicRead' ->
                  PkgSig bundle publicRead' pkg ->
                    hsame q q' ∧ hsame h h' ∧ UnaryHistory publicRead' ∧
                      PkgSig bundle publicRead' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier sameT sameW sameE terminalWindow terminalSeal terminalPublic publicPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      hUnary, cUnary, _pUnary, _nUnary, _m0m1u, _uvt, twq, qeh, _pPkg, _hn⟩
  have sameQ : hsame q q' :=
    cont_respects_hsame sameT sameW twq terminalWindow
  have sameH : hsame h h' :=
    cont_respects_hsame sameQ sameE qeh terminalSeal
  have hPrimeUnary : UnaryHistory h' :=
    unary_transport hUnary sameH
  have publicUnary : UnaryHistory publicRead' :=
    unary_cont_closed hPrimeUnary cUnary terminalPublic
  exact ⟨sameQ, sameH, publicUnary, publicPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
