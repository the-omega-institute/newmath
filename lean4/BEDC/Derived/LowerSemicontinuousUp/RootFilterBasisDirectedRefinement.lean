import BEDC.Derived.LowerSemicontinuousUp.RootEpigraphFilterDirectedness

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootFilterBasisDirectedRefinement [AskSetup] [PackageSetup]
    {X F E W R O H C P N thresholdLeft thresholdRight commonThreshold filterRead
      transported replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootEpigraphFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] ->
      UnaryHistory W ->
        UnaryHistory R ->
          UnaryHistory E ->
            UnaryHistory O ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory N ->
                    Cont W R thresholdLeft ->
                      Cont W R thresholdRight ->
                        Cont thresholdLeft thresholdRight commonThreshold ->
                          Cont commonThreshold E filterRead ->
                            Cont filterRead H transported ->
                              Cont transported C replayRead ->
                                Cont replayRead N namedRead ->
                                  PkgSig bundle P pkg ->
                                    PkgSig bundle N pkg ->
                                      UnaryHistory commonThreshold ∧ UnaryHistory filterRead ∧
                                        UnaryHistory transported ∧ UnaryHistory replayRead ∧
                                          UnaryHistory namedRead ∧
                                            Cont thresholdLeft thresholdRight commonThreshold ∧
                                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro fields wUnary rUnary eUnary _oUnary hUnary cUnary nUnary thresholdLeftRoute
    thresholdRightRoute commonRoute filterRoute transportRoute replayRoute namedRoute
    provenancePkg namePkg
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
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed filterUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportedUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary nUnary namedRoute
  exact
    ⟨commonUnary, filterUnary, transportedUnary, replayUnary, namedUnary, commonRoute,
      provenancePkg, namePkg⟩

end BEDC.Derived.LowerSemicontinuousUp
