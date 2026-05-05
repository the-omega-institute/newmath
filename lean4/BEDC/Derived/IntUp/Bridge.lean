import BEDC.Derived.IntUp.CanonicalReadback
import BEDC.Derived.IntUp.OneSidedContext
import BEDC.Derived.IntUp.HistorySemantic

namespace BEDC.Derived.IntUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem IntPairClassifier_contextual_canonical_pair_history_bridge_iff {a m n : BHist} :
    UnaryHistory a -> UnaryHistory m -> UnaryHistory n ->
      (IntPairClassifier (append a m, BHist.Empty) (append a n, BHist.Empty) ↔
        IntHistoryClassifier (BHist.e0 m) (BHist.e0 n)) ∧
      (IntPairClassifier (BHist.Empty, append m a) (BHist.Empty, append n a) ↔
        IntHistoryClassifier (BHist.e1 m) (BHist.e1 n)) := by
  intro unaryA _unaryM _unaryN
  have leftContext := (IntPairClassifier_one_sided_append_context_exactness
    (a := a) (p := m) (n := BHist.Empty) (q := n) (m := BHist.Empty) unaryA).left
  have rightContext := (IntPairClassifier_one_sided_append_context_exactness
    (a := a) (p := BHist.Empty) (n := m) (q := BHist.Empty) (m := n) unaryA).right
  have pairReadback := IntPairClassifier_canonical_same_sign_readback_iff (m := m) (n := n)
  have historyReadback := IntHistoryClassifier_same_tag_readback_iff (m := m) (n := n)
  constructor
  · constructor
    · intro contextual
      exact Iff.mpr historyReadback.left (Iff.mp pairReadback.left (Iff.mp leftContext contextual))
    · intro history
      exact Iff.mpr leftContext (Iff.mpr pairReadback.left (Iff.mp historyReadback.left history))
  · constructor
    · intro contextual
      exact Iff.mpr historyReadback.right (Iff.mp pairReadback.right (Iff.mp rightContext contextual))
    · intro history
      exact Iff.mpr rightContext (Iff.mpr pairReadback.right (Iff.mp historyReadback.right history))

end BEDC.Derived.IntUp
