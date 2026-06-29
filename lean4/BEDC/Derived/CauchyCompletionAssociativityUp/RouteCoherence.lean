import BEDC.Derived.CauchyCompletionAssociativityUp.FlatteningRoute

namespace BEDC.Derived.CauchyCompletionAssociativityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionAssociativityCarrier_route_coherence [AskSetup] [PackageSetup]
    {idempotence counit minimality stream dyadic regular real leftRoute rightRoute
      leftRoutePrime rightRoutePrime leftIdem rightIdem leftIdemPrime rightIdemPrime
      leftCounit rightCounit leftCounitPrime rightCounitPrime leftMinimal rightMinimal
      leftMinimalPrime rightMinimalPrime leftStream rightStream leftStreamPrime
      rightStreamPrime leftDyadic rightDyadic leftDyadicPrime rightDyadicPrime leftRegular
      rightRegular leftRegularPrime rightRegularPrime leftReal rightReal leftRealPrime
      rightRealPrime provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory leftRoute →
      UnaryHistory rightRoute →
        UnaryHistory leftRoutePrime →
          UnaryHistory rightRoutePrime →
            UnaryHistory idempotence →
              UnaryHistory counit →
                UnaryHistory minimality →
                  UnaryHistory stream →
                    UnaryHistory dyadic →
                      UnaryHistory regular →
                        UnaryHistory real →
                          hsame leftRoute leftRoutePrime →
                            hsame rightRoute rightRoutePrime →
                              hsame leftRoute rightRoute →
                                Cont leftRoute idempotence leftIdem →
                                  Cont rightRoute idempotence rightIdem →
                                    Cont leftRoutePrime idempotence leftIdemPrime →
                                      Cont rightRoutePrime idempotence rightIdemPrime →
                                        Cont leftIdem counit leftCounit →
                                          Cont rightIdem counit rightCounit →
                                            Cont leftIdemPrime counit leftCounitPrime →
                                              Cont rightIdemPrime counit rightCounitPrime →
                                                Cont leftCounit minimality leftMinimal →
                                                  Cont rightCounit minimality rightMinimal →
                                                    Cont leftCounitPrime minimality
                                                      leftMinimalPrime →
                                                      Cont rightCounitPrime minimality
                                                        rightMinimalPrime →
                                                        Cont leftMinimal stream
                                                          leftStream →
                                                          Cont rightMinimal stream
                                                            rightStream →
                                                            Cont leftMinimalPrime stream
                                                              leftStreamPrime →
                                                              Cont rightMinimalPrime stream
                                                                rightStreamPrime →
                                                                Cont leftStream dyadic
                                                                  leftDyadic →
                                                                  Cont rightStream dyadic
                                                                    rightDyadic →
                                                                    Cont leftStreamPrime dyadic
                                                                      leftDyadicPrime →
                                                                      Cont rightStreamPrime
                                                                        dyadic
                                                                        rightDyadicPrime →
                                                                        Cont leftDyadic regular
                                                                          leftRegular →
                                                                          Cont rightDyadic
                                                                            regular
                                                                            rightRegular →
                                                                            Cont leftDyadicPrime
                                                                              regular
                                                                              leftRegularPrime →
                                                                              Cont
                                                                                rightDyadicPrime
                                                                                regular
                                                                                rightRegularPrime →
                                                                                Cont leftRegular
                                                                                  real leftReal →
                                                                                  Cont rightRegular
                                                                                    real
                                                                                    rightReal →
                                                                                    Cont
                                                                                      leftRegularPrime
                                                                                      real
                                                                                      leftRealPrime →
                                                                                      Cont
                                                                                        rightRegularPrime
                                                                                        real
                                                                                        rightRealPrime →
                                                                                        PkgSig bundle
                                                                                          provenance
                                                                                          pkg →
                                                                                          PkgSig bundle
                                                                                            leftReal
                                                                                            pkg →
                                                                                            PkgSig
                                                                                              bundle
                                                                                              rightReal
                                                                                              pkg →
                                                                                              hsame
                                                                                                leftReal
                                                                                                leftRealPrime ∧
                                                                                                hsame
                                                                                                  rightReal
                                                                                                  rightRealPrime ∧
                                                                                                  hsame
                                                                                                    leftReal
                                                                                                    rightReal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro leftUnary rightUnary leftPrimeUnary rightPrimeUnary idemUnary counitUnary
    minimalUnary streamUnary dyadicUnary regularUnary realUnary sameLeftRoute sameRightRoute
    sameRoute leftIdemRoute rightIdemRoute leftIdemPrimeRoute rightIdemPrimeRoute
    leftCounitRoute rightCounitRoute leftCounitPrimeRoute rightCounitPrimeRoute
    leftMinimalRoute rightMinimalRoute leftMinimalPrimeRoute rightMinimalPrimeRoute
    leftStreamRoute rightStreamRoute leftStreamPrimeRoute rightStreamPrimeRoute leftDyadicRoute
    rightDyadicRoute leftDyadicPrimeRoute rightDyadicPrimeRoute leftRegularRoute
    rightRegularRoute leftRegularPrimeRoute rightRegularPrimeRoute leftRealRoute rightRealRoute
    leftRealPrimeRoute rightRealPrimeRoute provenancePkg leftPkg rightPkg
  have sameLeftIdem : hsame leftIdem leftIdemPrime :=
    cont_respects_hsame sameLeftRoute (hsame_refl idempotence) leftIdemRoute
      leftIdemPrimeRoute
  have sameLeftCounit : hsame leftCounit leftCounitPrime :=
    cont_respects_hsame sameLeftIdem (hsame_refl counit) leftCounitRoute
      leftCounitPrimeRoute
  have sameLeftMinimal : hsame leftMinimal leftMinimalPrime :=
    cont_respects_hsame sameLeftCounit (hsame_refl minimality) leftMinimalRoute
      leftMinimalPrimeRoute
  have sameLeftStream : hsame leftStream leftStreamPrime :=
    cont_respects_hsame sameLeftMinimal (hsame_refl stream) leftStreamRoute
      leftStreamPrimeRoute
  have sameLeftDyadic : hsame leftDyadic leftDyadicPrime :=
    cont_respects_hsame sameLeftStream (hsame_refl dyadic) leftDyadicRoute
      leftDyadicPrimeRoute
  have sameLeftRegular : hsame leftRegular leftRegularPrime :=
    cont_respects_hsame sameLeftDyadic (hsame_refl regular) leftRegularRoute
      leftRegularPrimeRoute
  have sameLeftReal : hsame leftReal leftRealPrime :=
    cont_respects_hsame sameLeftRegular (hsame_refl real) leftRealRoute leftRealPrimeRoute
  have sameRightIdem : hsame rightIdem rightIdemPrime :=
    cont_respects_hsame sameRightRoute (hsame_refl idempotence) rightIdemRoute
      rightIdemPrimeRoute
  have sameRightCounit : hsame rightCounit rightCounitPrime :=
    cont_respects_hsame sameRightIdem (hsame_refl counit) rightCounitRoute
      rightCounitPrimeRoute
  have sameRightMinimal : hsame rightMinimal rightMinimalPrime :=
    cont_respects_hsame sameRightCounit (hsame_refl minimality) rightMinimalRoute
      rightMinimalPrimeRoute
  have sameRightStream : hsame rightStream rightStreamPrime :=
    cont_respects_hsame sameRightMinimal (hsame_refl stream) rightStreamRoute
      rightStreamPrimeRoute
  have sameRightDyadic : hsame rightDyadic rightDyadicPrime :=
    cont_respects_hsame sameRightStream (hsame_refl dyadic) rightDyadicRoute
      rightDyadicPrimeRoute
  have sameRightRegular : hsame rightRegular rightRegularPrime :=
    cont_respects_hsame sameRightDyadic (hsame_refl regular) rightRegularRoute
      rightRegularPrimeRoute
  have sameRightReal : hsame rightReal rightRealPrime :=
    cont_respects_hsame sameRightRegular (hsame_refl real) rightRealRoute rightRealPrimeRoute
  have sameReal : hsame leftReal rightReal :=
    CauchyCompletionAssociativityFlatteningRoute leftUnary rightUnary idemUnary counitUnary
      minimalUnary streamUnary dyadicUnary regularUnary realUnary sameRoute leftIdemRoute
      rightIdemRoute leftCounitRoute rightCounitRoute leftMinimalRoute rightMinimalRoute
      leftStreamRoute rightStreamRoute leftDyadicRoute rightDyadicRoute leftRegularRoute
      rightRegularRoute leftRealRoute rightRealRoute provenancePkg leftPkg rightPkg
  exact ⟨sameLeftReal, sameRightReal, sameReal⟩

end BEDC.Derived.CauchyCompletionAssociativityUp
