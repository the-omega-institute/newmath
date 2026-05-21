import BEDC.Derived.DiagonalCofinalTailUp

namespace BEDC.Derived.DiagonalCofinalTailUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalCofinalTailCarrier_tastegate_flow_recognition
    [AskSetup] [PackageSetup]
    {q s g d r w h c p n recognizedFlow tasteRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg ->
      Cont q s recognizedFlow ->
        Cont recognizedFlow c tasteRead ->
          PkgSig bundle tasteRead pkg ->
            UnaryHistory recognizedFlow ∧ UnaryHistory tasteRead ∧
              Cont q s recognizedFlow ∧ Cont recognizedFlow c tasteRead ∧
                PkgSig bundle p pkg ∧ PkgSig bundle tasteRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier recognizedRoute tasteRoute tastePkg
  obtain ⟨qUnary, sUnary, _gUnary, _dUnary, _rUnary, _wUnary, _hUnary, cUnary,
    _pUnary, _nUnary, _qsRoute, _gdRoute, _whRoute, pPkg⟩ := carrier
  have recognizedUnary : UnaryHistory recognizedFlow :=
    unary_cont_closed qUnary sUnary recognizedRoute
  have tasteUnary : UnaryHistory tasteRead :=
    unary_cont_closed recognizedUnary cUnary tasteRoute
  exact ⟨recognizedUnary, tasteUnary, recognizedRoute, tasteRoute, pPkg, tastePkg⟩

end BEDC.Derived.DiagonalCofinalTailUp
