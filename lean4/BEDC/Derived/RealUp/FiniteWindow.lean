import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

def UnaryOffsetLe (k w : BHist) : Prop :=
  UnaryHistory k ∧ ∃ tail : BHist, UnaryHistory tail ∧ Cont k tail w

def RealUnaryStreamWindowClassifier (s t : BHist -> BHist) (a w : BHist) : Prop :=
  UnaryHistory a ∧ UnaryHistory w ∧
    ∀ k : BHist, UnaryOffsetLe k w ->
      RatHistoryClassifier (s (append a k)) (t (append a k))

theorem RealUnaryStreamWindowClassifier_coverage {s t : BHist -> BHist} {a w : BHist} :
    RealUnaryStreamClassifier s t -> UnaryHistory a -> UnaryHistory w ->
      RealUnaryStreamWindowClassifier s t a w := by
  intro classified aUnary wUnary
  constructor
  · exact aUnary
  · constructor
    · exact wUnary
    · intro k offset
      exact classified (append a k) (unary_append_closed aUnary offset.left)

end BEDC.Derived.RealUp
