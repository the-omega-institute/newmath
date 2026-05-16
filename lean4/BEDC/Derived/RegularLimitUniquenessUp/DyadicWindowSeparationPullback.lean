import BEDC.Derived.RegularLimitUniquenessUp

/-!
# RegularLimitUniquenessUp dyadic window separation pullback.
-/

namespace BEDC.Derived.RegularLimitUniquenessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularLimitUniquenessCarrier_dyadic_window_separation_pullback
    [AskSetup] [PackageSetup]
    {family diagonalLeft diagonalRight threshold readbackLeft readbackRight sealLeft sealRight
      separated transport route provenance localCert endpoint dyadicWindow leftWindow rightWindow
      leftPullback rightPullback comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLimitUniquenessCarrier family diagonalLeft diagonalRight threshold readbackLeft
        readbackRight sealLeft sealRight separated transport route provenance localCert endpoint
        bundle pkg ->
      UnaryHistory dyadicWindow ->
        Cont readbackLeft dyadicWindow leftWindow ->
          Cont readbackRight dyadicWindow rightWindow ->
            Cont leftWindow sealLeft leftPullback ->
              Cont rightWindow sealRight rightPullback ->
                Cont leftPullback rightPullback comparisonRead ->
                  PkgSig bundle comparisonRead pkg ->
                    UnaryHistory leftWindow ∧ UnaryHistory rightWindow ∧
                      UnaryHistory leftPullback ∧ UnaryHistory rightPullback ∧
                        UnaryHistory comparisonRead ∧
                          Cont readbackLeft dyadicWindow leftWindow ∧
                            Cont readbackRight dyadicWindow rightWindow ∧
                              Cont leftWindow sealLeft leftPullback ∧
                                Cont rightWindow sealRight rightPullback ∧
                                  Cont leftPullback rightPullback comparisonRead ∧
                                    PkgSig bundle endpoint pkg ∧
                                      PkgSig bundle comparisonRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier dyadicUnary leftWindowRoute rightWindowRoute leftPullbackRoute
    rightPullbackRoute comparisonRoute comparisonPkg
  obtain ⟨_familyUnary, _diagonalLeftUnary, _diagonalRightUnary, thresholdUnary,
    readbackLeftUnary, readbackRightUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localCertUnary, _familyThresholdDiagonalLeft, _familyThresholdDiagonalRight,
    _diagonalLeftThresholdReadback, _diagonalRightThresholdReadback,
    readbackLeftThresholdSeal, readbackRightThresholdSeal, _sealComparison,
    _separatedTransportEndpoint, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have sealLeftUnary : UnaryHistory sealLeft :=
    unary_cont_closed readbackLeftUnary thresholdUnary readbackLeftThresholdSeal
  have sealRightUnary : UnaryHistory sealRight :=
    unary_cont_closed readbackRightUnary thresholdUnary readbackRightThresholdSeal
  have leftWindowUnary : UnaryHistory leftWindow :=
    unary_cont_closed readbackLeftUnary dyadicUnary leftWindowRoute
  have rightWindowUnary : UnaryHistory rightWindow :=
    unary_cont_closed readbackRightUnary dyadicUnary rightWindowRoute
  have leftPullbackUnary : UnaryHistory leftPullback :=
    unary_cont_closed leftWindowUnary sealLeftUnary leftPullbackRoute
  have rightPullbackUnary : UnaryHistory rightPullback :=
    unary_cont_closed rightWindowUnary sealRightUnary rightPullbackRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed leftPullbackUnary rightPullbackUnary comparisonRoute
  exact
    ⟨leftWindowUnary, rightWindowUnary, leftPullbackUnary, rightPullbackUnary,
      comparisonUnary, leftWindowRoute, rightWindowRoute, leftPullbackRoute,
      rightPullbackRoute, comparisonRoute, endpointPkg, comparisonPkg⟩

end BEDC.Derived.RegularLimitUniquenessUp
