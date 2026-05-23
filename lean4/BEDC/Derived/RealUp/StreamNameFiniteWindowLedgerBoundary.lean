import BEDC.Derived.RealUp.Core
import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Bundle
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp
open BEDC.Derived.StreamNameUp

theorem RealupStreamnameFiniteWindowLedgerBoundary {h k d e : BHist}
    {bundle : ProbeBundle BHist} :
    (exists n : BHist, InBundle n bundle ∧ UnaryHistory n) ->
      RealConstantHistoryClassifier h k ->
        hsame h (BHist.e1 (BHist.e1 d)) ->
          hsame k (BHist.e1 (BHist.e1 e)) ->
            RatStreamNameFiniteWindowClassifier (RatConstStream (BHist.e1 d))
                (RatConstStream (BHist.e1 e)) bundle ∧
              RatHistoryClassifier (BHist.e1 d) (BHist.e1 e) ∧ UnaryHistory d ∧
                UnaryHistory e ∧ hsame d e := by
  -- BEDC touchpoint anchor: BHist ProbeBundle InBundle hsame RatHistoryClassifier
  intro bundleWitness realClassifier sameH sameK
  have ratClassifier : RatHistoryClassifier (BHist.e1 d) (BHist.e1 e) :=
    RealConstantHistoryClassifier_e1_tail_readback realClassifier sameH sameK
  have windowClassifier :
      RatStreamNameFiniteWindowClassifier (RatConstStream (BHist.e1 d))
        (RatConstStream (BHist.e1 e)) bundle :=
    Iff.mpr (RatStreamNameFiniteWindowClassifier_constant_exactness bundleWitness)
      ratClassifier
  have tailRows : UnaryHistory d ∧ UnaryHistory e ∧ hsame d e :=
    RatHistoryClassifier_e1_tail_unary_iff.mp ratClassifier
  exact
    ⟨windowClassifier, ratClassifier, tailRows.left, tailRows.right.left,
      tailRows.right.right⟩

end BEDC.Derived.RealUp
