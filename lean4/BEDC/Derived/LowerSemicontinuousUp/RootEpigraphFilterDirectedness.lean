import BEDC.Derived.LowerSemicontinuousUp.EpigraphFilterRoute

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootEpigraphFilterDirectedness [AskSetup] [PackageSetup]
    {X F E W R O H C P N thresholdLeft thresholdRight commonThreshold filterRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootEpigraphFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] ->
      UnaryHistory W ->
        UnaryHistory R ->
          UnaryHistory E ->
            UnaryHistory O ->
              UnaryHistory C ->
                UnaryHistory N ->
                  Cont W R thresholdLeft ->
                    Cont W R thresholdRight ->
                      Cont thresholdLeft thresholdRight commonThreshold ->
                        Cont commonThreshold E filterRead ->
                          Cont filterRead N namedRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle N pkg ->
                                UnaryHistory commonThreshold ∧ UnaryHistory filterRead ∧
                                  UnaryHistory namedRead ∧
                                    Cont thresholdLeft thresholdRight commonThreshold ∧
                                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro fields wUnary rUnary eUnary _oUnary _cUnary nUnary thresholdLeftRoute
    thresholdRightRoute commonRoute filterRoute namedRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootEpigraphFields
          (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] := fields
  have thresholdLeftUnary : UnaryHistory thresholdLeft :=
    unary_cont_closed wUnary rUnary thresholdLeftRoute
  have thresholdRightUnary : UnaryHistory thresholdRight :=
    unary_cont_closed wUnary rUnary thresholdRightRoute
  have commonUnary : UnaryHistory commonThreshold :=
    unary_cont_closed thresholdLeftUnary thresholdRightUnary commonRoute
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed commonUnary eUnary filterRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed filterUnary nUnary namedRoute
  exact ⟨commonUnary, filterUnary, namedUnary, commonRoute, provenancePkg, namePkg⟩

end BEDC.Derived.LowerSemicontinuousUp
