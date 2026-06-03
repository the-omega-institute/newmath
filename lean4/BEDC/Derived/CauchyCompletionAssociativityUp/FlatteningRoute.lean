import BEDC.Derived.CauchyCompletionAssociativityUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionAssociativityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionAssociativityFlatteningRoute [AskSetup] [PackageSetup]
    {leftRoute rightRoute idempotence counit minimality stream dyadic regular real leftIdem
      rightIdem leftCounit rightCounit leftMinimal rightMinimal leftStream rightStream
      leftDyadic rightDyadic leftRegular rightRegular leftReal rightReal provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory leftRoute →
      UnaryHistory rightRoute →
        UnaryHistory idempotence →
          UnaryHistory counit →
            UnaryHistory minimality →
              UnaryHistory stream →
                UnaryHistory dyadic →
                  UnaryHistory regular →
                    UnaryHistory real →
                      hsame leftRoute rightRoute →
                        Cont leftRoute idempotence leftIdem →
                          Cont rightRoute idempotence rightIdem →
                            Cont leftIdem counit leftCounit →
                              Cont rightIdem counit rightCounit →
                                Cont leftCounit minimality leftMinimal →
                                  Cont rightCounit minimality rightMinimal →
                                    Cont leftMinimal stream leftStream →
                                      Cont rightMinimal stream rightStream →
                                        Cont leftStream dyadic leftDyadic →
                                          Cont rightStream dyadic rightDyadic →
                                            Cont leftDyadic regular leftRegular →
                                              Cont rightDyadic regular rightRegular →
                                                Cont leftRegular real leftReal →
                                                  Cont rightRegular real rightReal →
                                                    PkgSig bundle provenance pkg →
                                                      PkgSig bundle leftReal pkg →
                                                        PkgSig bundle rightReal pkg →
                                                          hsame leftReal rightReal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame
  intro leftUnary rightUnary idemUnary counitUnary minimalUnary streamUnary dyadicUnary
    regularUnary realUnary sameRoute leftIdemRoute rightIdemRoute leftCounitRoute
    rightCounitRoute leftMinimalRoute rightMinimalRoute leftStreamRoute rightStreamRoute
    leftDyadicRoute rightDyadicRoute leftRegularRoute rightRegularRoute leftRealRoute
    rightRealRoute _provenancePkg _leftPkg _rightPkg
  have sameIdem : hsame leftIdem rightIdem :=
    cont_respects_hsame sameRoute (hsame_refl idempotence) leftIdemRoute rightIdemRoute
  have sameCounit : hsame leftCounit rightCounit :=
    cont_respects_hsame sameIdem (hsame_refl counit) leftCounitRoute rightCounitRoute
  have sameMinimal : hsame leftMinimal rightMinimal :=
    cont_respects_hsame sameCounit (hsame_refl minimality) leftMinimalRoute
      rightMinimalRoute
  have sameStream : hsame leftStream rightStream :=
    cont_respects_hsame sameMinimal (hsame_refl stream) leftStreamRoute rightStreamRoute
  have sameDyadic : hsame leftDyadic rightDyadic :=
    cont_respects_hsame sameStream (hsame_refl dyadic) leftDyadicRoute rightDyadicRoute
  have sameRegular : hsame leftRegular rightRegular :=
    cont_respects_hsame sameDyadic (hsame_refl regular) leftRegularRoute rightRegularRoute
  exact cont_respects_hsame sameRegular (hsame_refl real) leftRealRoute rightRealRoute

end BEDC.Derived.CauchyCompletionAssociativityUp
