import BEDC.Derived.RealUp.FiniteWindow

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealUnaryStreamWindowClassifier_endpoint_at_bound {s t : BHist -> BHist}
    {a w : BHist} :
    RealUnaryStreamWindowClassifier s t a w ->
      RatHistoryClassifier (s (append a w)) (t (append a w)) := by
  intro windowed
  have offset : UnaryOffsetLe w w :=
    ⟨windowed.right.left, ⟨BHist.Empty, unary_empty, cont_right_unit w⟩⟩
  exact windowed.right.right w offset

end BEDC.Derived.RealUp
