import BEDC.Derived.StreamNameUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Package

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem StreamNameRealSealFactorizationBoundary [AskSetup] [PackageSetup]
    {s t : BHist -> BHist} {window : ProbeBundle BHist} {bundle : ProbeBundle ProbeName}
    {left right dyadicLedger handoff regseqSeal realRead : BHist} {pkg : Pkg} :
    RatStreamNameFiniteWindowClassifier s t window ->
      InBundle left window ->
        InBundle right window ->
          UnaryHistory left ->
            UnaryHistory right ->
              UnaryHistory dyadicLedger ->
                UnaryHistory regseqSeal ->
                  hsame dyadicLedger (append left right) ->
                    Cont (s left) (t right) handoff ->
                      Cont handoff regseqSeal realRead ->
                        PkgSig bundle realRead pkg ->
                          RatHistoryClassifier (s left) (t left) ∧
                            RatHistoryClassifier (s right) (t right) ∧
                              UnaryHistory dyadicLedger ∧ UnaryHistory handoff ∧
                                UnaryHistory realRead ∧ hsame dyadicLedger (append left right) ∧
                                  Cont (s left) (t right) handoff ∧
                                    Cont handoff regseqSeal realRead ∧
                                      PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame
  intro finiteWindow leftMember rightMember leftUnary rightUnary dyadicUnary regseqUnary
    sameDyadic handoffRoute realRoute pkgRow
  have leftClassified : RatHistoryClassifier (s left) (t left) :=
    finiteWindow left leftMember leftUnary
  have rightClassified : RatHistoryClassifier (s right) (t right) :=
    finiteWindow right rightMember rightUnary
  have sLeftPositive : PositiveUnaryDenominator (s left) :=
    (RatHistoryClassifier_positive_denominators leftClassified).left
  have tRightPositive : PositiveUnaryDenominator (t right) :=
    (RatHistoryClassifier_positive_denominators rightClassified).right
  have sLeftUnary : UnaryHistory (s left) :=
    (PositiveUnaryDenominator_unary_and_nonempty sLeftPositive).left
  have tRightUnary : UnaryHistory (t right) :=
    (PositiveUnaryDenominator_unary_and_nonempty tRightPositive).left
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed sLeftUnary tRightUnary handoffRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed handoffUnary regseqUnary realRoute
  exact
    ⟨leftClassified, rightClassified, dyadicUnary, handoffUnary, realUnary, sameDyadic,
      handoffRoute, realRoute, pkgRow⟩

end BEDC.Derived.StreamNameUp
