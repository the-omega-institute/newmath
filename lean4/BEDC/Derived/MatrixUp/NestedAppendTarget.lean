import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem MatrixSingletonNestedAppendTarget_continuation_result_iff {M N P h r : BHist} :
    Cont h (append M (append N P)) r ->
      (MatrixSingletonCarrier r ↔
        MatrixSingletonCarrier h ∧ MatrixSingletonCarrier M ∧
          MatrixSingletonCarrier N ∧ MatrixSingletonCarrier P) := by
  intro continuation
  constructor
  · intro resultCarrier
    have emptyContinuation : Cont h (append M (append N P)) BHist.Empty :=
      cont_result_hsame_transport continuation resultCarrier
    have endpoints := cont_empty_result_inversion emptyContinuation
    have targetParts := append_eq_empty_iff.mp endpoints.right
    have nestedParts := append_eq_empty_iff.mp targetParts.right
    exact And.intro endpoints.left
      (And.intro targetParts.left (And.intro nestedParts.left nestedParts.right))
  · intro carriers
    have targetCarrier : MatrixSingletonCarrier (append M (append N P)) :=
      append_eq_empty_iff.mpr
        (And.intro carriers.right.left
          (append_eq_empty_iff.mpr
            (And.intro carriers.right.right.left carriers.right.right.right)))
    exact cont_respects_hsame carriers.left targetCarrier continuation (cont_right_unit BHist.Empty)

end BEDC.Derived.MatrixUp
