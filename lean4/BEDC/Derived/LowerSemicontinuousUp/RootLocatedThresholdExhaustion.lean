import BEDC.Derived.LowerSemicontinuousUp.RootLocatedReadback

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootLocatedThresholdExhaustion [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead epigraphRead locatedRead transportRead replayRead
      thresholdRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory W -> UnaryHistory R -> UnaryHistory E -> UnaryHistory O ->
        UnaryHistory H -> UnaryHistory C -> UnaryHistory N -> Cont W R windowRead ->
          Cont windowRead E epigraphRead -> Cont epigraphRead O locatedRead ->
            Cont locatedRead H transportRead -> Cont transportRead C replayRead ->
              Cont replayRead N thresholdRead -> PkgSig bundle P pkg ->
                PkgSig bundle N pkg ->
                  UnaryHistory thresholdRead ∧ Cont replayRead N thresholdRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                      hsame thresholdRead thresholdRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro fields wUnary rUnary eUnary oUnary hUnary cUnary nUnary windowRoute epigraphRoute
    locatedRoute transportRoute replayRoute thresholdRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed locatedUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed replayUnary nUnary thresholdRoute
  exact
    ⟨thresholdUnary, thresholdRoute, provenancePkg, namePkg, hsame_refl thresholdRead⟩

end BEDC.Derived.LowerSemicontinuousUp
