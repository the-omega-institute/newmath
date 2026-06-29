import BEDC.Derived.CofinalStreamTailSelectorUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.CofinalStreamTailSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CofinalStreamTailSelectorObligationPackage [AskSetup] [PackageSetup]
    {epsilon W R D A sigma H C P N windowRead dyadicRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalStreamTailSelectorCarrier epsilon W R D A sigma H C P N bundle pkg →
      Cont epsilon W windowRead →
        Cont windowRead D dyadicRead →
          Cont dyadicRead A sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory epsilon ∧ UnaryHistory W ∧ UnaryHistory D ∧
                UnaryHistory A ∧ UnaryHistory windowRead ∧ UnaryHistory dyadicRead ∧
                  UnaryHistory sealRead ∧ Cont epsilon W windowRead ∧
                    Cont windowRead D dyadicRead ∧ Cont dyadicRead A sealRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier windowRoute dyadicRoute sealRoute sealPkg
  obtain ⟨epsilonUnary, wUnary, _rUnary, dUnary, aUnary, _sigmaUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, pPkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed epsilonUnary wUnary windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary dUnary dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary aUnary sealRoute
  exact
    ⟨epsilonUnary, wUnary, dUnary, aUnary, windowUnary, dyadicUnary, sealUnary,
      windowRoute, dyadicRoute, sealRoute, pPkg, sealPkg⟩

end BEDC.Derived.CofinalStreamTailSelectorUp
