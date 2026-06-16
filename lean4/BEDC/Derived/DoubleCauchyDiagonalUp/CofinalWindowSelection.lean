import BEDC.Derived.DoubleCauchyDiagonalUp

namespace BEDC.Derived.DoubleCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DoubleCauchyDiagonalCofinalWindowSelection [AskSetup] [PackageSetup]
    {R W D K H C P N windowRead regularRead dyadicRead selectedWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DoubleCauchyDiagonalCarrier R W D K H C P N bundle pkg →
      Cont W R regularRead →
        Cont regularRead D dyadicRead →
          Cont dyadicRead K selectedWindow →
            PkgSig bundle selectedWindow pkg →
              UnaryHistory regularRead ∧ UnaryHistory dyadicRead ∧
                UnaryHistory selectedWindow ∧ PkgSig bundle selectedWindow pkg ∧
                  hsame selectedWindow selectedWindow := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory hsame
  intro carrier windowRoute dyadicRoute selectionRoute selectedPkg
  obtain ⟨rUnary, wUnary, dUnary, kUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _regularWindowRoute, _diagonalDyadicRoute, _transportRoute, _provenancePkg,
    _localNamePkg⟩ := carrier
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed regularUnary dUnary dyadicRoute
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed dyadicUnary kUnary selectionRoute
  exact ⟨regularUnary, dyadicUnary, selectedUnary, selectedPkg, hsame_refl selectedWindow⟩

end BEDC.Derived.DoubleCauchyDiagonalUp
