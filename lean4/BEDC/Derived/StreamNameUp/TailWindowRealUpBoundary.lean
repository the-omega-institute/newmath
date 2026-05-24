import BEDC.Derived.StreamNameUp.RealSealFactorizationBoundary

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem StreamNameTailWindowRealUpBoundary [AskSetup] [PackageSetup]
    {s t : BHist -> BHist} {window : ProbeBundle BHist} {bundle : ProbeBundle ProbeName}
    {left right dyadicLedger handoff regseqSeal realRead boundaryRead : BHist} {pkg : Pkg} :
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
                        Cont realRead dyadicLedger boundaryRead ->
                          PkgSig bundle realRead pkg ->
                            PkgSig bundle boundaryRead pkg ->
                              RatHistoryClassifier (s left) (t left) ∧
                                RatHistoryClassifier (s right) (t right) ∧
                                  UnaryHistory handoff ∧
                                    UnaryHistory realRead ∧
                                      UnaryHistory boundaryRead ∧
                                        hsame dyadicLedger (append left right) ∧
                                          Cont handoff regseqSeal realRead ∧
                                            Cont realRead dyadicLedger boundaryRead ∧
                                              PkgSig bundle realRead pkg ∧
                                                PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame UnaryHistory
  intro finiteWindow leftMember rightMember leftUnary rightUnary dyadicUnary regseqUnary
    sameDyadic handoffRoute realRoute boundaryRoute realPkg boundaryPkg
  have baseRows :
      RatHistoryClassifier (s left) (t left) ∧
        RatHistoryClassifier (s right) (t right) ∧
          UnaryHistory dyadicLedger ∧ UnaryHistory handoff ∧
            UnaryHistory realRead ∧ hsame dyadicLedger (append left right) ∧
              Cont (s left) (t right) handoff ∧
                Cont handoff regseqSeal realRead ∧ PkgSig bundle realRead pkg :=
    StreamNameRealSealFactorizationBoundary finiteWindow leftMember rightMember leftUnary
      rightUnary dyadicUnary regseqUnary sameDyadic handoffRoute realRoute realPkg
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed baseRows.right.right.right.right.left baseRows.right.right.left boundaryRoute
  exact
    ⟨baseRows.left, baseRows.right.left, baseRows.right.right.right.left,
      baseRows.right.right.right.right.left, boundaryUnary, baseRows.right.right.right.right.right.left,
      baseRows.right.right.right.right.right.right.right.left, boundaryRoute,
      baseRows.right.right.right.right.right.right.right.right, boundaryPkg⟩

end BEDC.Derived.StreamNameUp
