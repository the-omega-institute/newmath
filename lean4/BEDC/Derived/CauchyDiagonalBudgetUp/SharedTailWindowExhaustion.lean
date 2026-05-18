import BEDC.Derived.CauchyDiagonalBudgetUp

namespace BEDC.Derived.CauchyDiagonalBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyDiagonalBudgetCarrier_shared_tail_window_exhaustion
    [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name tail compare sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg ->
      Cont m w tail ->
        Cont tail d compare ->
          hsame compare k ->
            Cont compare s sealRead ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory tail ∧ UnaryHistory compare ∧ UnaryHistory sealRead ∧
                  hsame compare k ∧ Cont m w tail ∧ Cont tail d compare ∧
                    Cont compare s sealRead ∧ PkgSig bundle p pkg ∧
                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier mWindowTail tailDCompare compareSameK compareSSeal sealPkg
  obtain ⟨_epsilonUnary, mUnary, wUnary, dUnary, _kUnary, sUnary, _hUnary, _cUnary,
    _pUnary, _nameUnary, _epsilonMW, _wDK, _kSH, _hCP, _cPName, pPkg⟩ := carrier
  have tailUnary : UnaryHistory tail :=
    unary_cont_closed mUnary wUnary mWindowTail
  have compareUnary : UnaryHistory compare :=
    unary_cont_closed tailUnary dUnary tailDCompare
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed compareUnary sUnary compareSSeal
  exact
    ⟨tailUnary, compareUnary, sealUnary, compareSameK, mWindowTail, tailDCompare,
      compareSSeal, pPkg, sealPkg⟩

end BEDC.Derived.CauchyDiagonalBudgetUp
