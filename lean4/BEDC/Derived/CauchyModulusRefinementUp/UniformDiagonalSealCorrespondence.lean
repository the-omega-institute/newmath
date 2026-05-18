import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_uniform_diagonal_seal_correspondence
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n uniformRead diagonalRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w uniformRead ->
        Cont uniformRead q diagonalRead ->
          Cont diagonalRead e terminalRead ->
            PkgSig bundle terminalRead pkg ->
              UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧
                UnaryHistory uniformRead ∧ UnaryHistory diagonalRead ∧
                  UnaryHistory terminalRead ∧ Cont t w uniformRead ∧
                    Cont uniformRead q diagonalRead ∧ Cont diagonalRead e terminalRead ∧
                      Cont q e h ∧ PkgSig bundle p pkg ∧
                        PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier uniformRoute diagonalRoute terminalRoute terminalPkg
  obtain ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, qeh, pPkg, _hn⟩ :=
    carrier
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed tUnary wUnary uniformRoute
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed uniformReadUnary qUnary diagonalRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed diagonalReadUnary eUnary terminalRoute
  exact
    ⟨tUnary, wUnary, qUnary, eUnary, uniformReadUnary, diagonalReadUnary,
      terminalReadUnary, uniformRoute, diagonalRoute, terminalRoute, qeh, pPkg,
      terminalPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
