import BEDC.Derived.StreamNameUp.PointwiseHandoff

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem StreamNameRegSeqRatPointwiseHandoffExhaustion {s t : BHist -> BHist}
    {bundle : ProbeBundle BHist} {left right dyadicLedger handoff : BHist} :
    RatStreamNameFiniteWindowClassifier s t bundle ->
      InBundle left bundle ->
        InBundle right bundle ->
          UnaryHistory left ->
            UnaryHistory right ->
              UnaryHistory dyadicLedger ->
                hsame dyadicLedger (append left right) ->
                  Cont (s left) (t right) handoff ->
                    RatHistoryClassifier (s left) (t left) ∧
                      RatHistoryClassifier (s right) (t right) ∧
                        UnaryHistory dyadicLedger ∧ hsame dyadicLedger (append left right) ∧
                          Cont (s left) (t right) handoff := by
  -- BEDC touchpoint anchor: BHist ProbeBundle InBundle hsame Cont UnaryHistory
  intro classifier leftMember rightMember leftUnary rightUnary dyadicUnary sameDyadic handoffCont
  have leftClassified : RatHistoryClassifier (s left) (t left) :=
    classifier left leftMember leftUnary
  have rightClassified : RatHistoryClassifier (s right) (t right) :=
    classifier right rightMember rightUnary
  exact ⟨leftClassified, rightClassified, dyadicUnary, sameDyadic, handoffCont⟩

end BEDC.Derived.StreamNameUp
