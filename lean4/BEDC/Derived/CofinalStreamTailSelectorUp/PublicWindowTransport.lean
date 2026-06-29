import BEDC.Derived.CofinalStreamTailSelectorUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.CofinalStreamTailSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CofinalStreamTailSelectorPublicWindowTransport [AskSetup] [PackageSetup]
    {epsilon W R D A sigma H C P N epsilonWindow windowRegular regularDyadic
      dyadicSelector selectorSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalStreamTailSelectorCarrier epsilon W R D A sigma H C P N bundle pkg →
      Cont epsilon W epsilonWindow →
        Cont epsilonWindow R windowRegular →
          Cont windowRegular D regularDyadic →
            Cont regularDyadic sigma dyadicSelector →
              Cont dyadicSelector A selectorSeal →
                UnaryHistory epsilonWindow ∧
                  UnaryHistory windowRegular ∧
                    UnaryHistory regularDyadic ∧
                      UnaryHistory dyadicSelector ∧
                        UnaryHistory selectorSeal ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier epsilonRoute regularRoute dyadicRoute selectorRoute sealRoute
  obtain ⟨epsilonUnary, windowUnary, regularUnary, dyadicUnary, selectorUnary,
    sigmaUnary, _handoffUnary, _contReplayUnary, _pkgUnary, _localUnary, packageProof⟩ :=
    carrier
  have epsilonWindowUnary : UnaryHistory epsilonWindow :=
    unary_cont_closed epsilonUnary windowUnary epsilonRoute
  have windowRegularUnary : UnaryHistory windowRegular :=
    unary_cont_closed epsilonWindowUnary regularUnary regularRoute
  have regularDyadicUnary : UnaryHistory regularDyadic :=
    unary_cont_closed windowRegularUnary dyadicUnary dyadicRoute
  have dyadicSelectorUnary : UnaryHistory dyadicSelector :=
    unary_cont_closed regularDyadicUnary sigmaUnary selectorRoute
  have selectorSealUnary : UnaryHistory selectorSeal :=
    unary_cont_closed dyadicSelectorUnary selectorUnary sealRoute
  exact
    ⟨epsilonWindowUnary, windowRegularUnary, regularDyadicUnary, dyadicSelectorUnary,
      selectorSealUnary, packageProof⟩

end BEDC.Derived.CofinalStreamTailSelectorUp
