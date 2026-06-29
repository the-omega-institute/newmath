import BEDC.Derived.CofinalStreamTailSelectorUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.CofinalStreamTailSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CofinalStreamTailSelectorScopedRoute [AskSetup] [PackageSetup]
    {epsilon W R D A sigma H C P N windowRead regularRead dyadicRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalStreamTailSelectorCarrier epsilon W R D A sigma H C P N bundle pkg →
      Cont epsilon W windowRead →
        Cont windowRead R regularRead →
          Cont regularRead D dyadicRead →
            Cont dyadicRead A sealRead →
              PkgSig bundle P pkg →
                PkgSig bundle sealRead pkg →
                  UnaryHistory epsilon ∧ UnaryHistory W ∧ UnaryHistory R ∧
                    UnaryHistory D ∧ UnaryHistory A ∧ UnaryHistory windowRead ∧
                      UnaryHistory regularRead ∧ UnaryHistory dyadicRead ∧
                        UnaryHistory sealRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier windowRoute regularRoute dyadicRoute sealRoute packageProof sealPkg
  obtain ⟨epsilonUnary, wUnary, rUnary, dUnary, aUnary, _sigmaUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _carrierPkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed epsilonUnary wUnary windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary rUnary regularRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed regularUnary dUnary dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary aUnary sealRoute
  exact
    ⟨epsilonUnary, wUnary, rUnary, dUnary, aUnary, windowUnary, regularUnary,
      dyadicUnary, sealUnary, packageProof, sealPkg⟩

end BEDC.Derived.CofinalStreamTailSelectorUp
