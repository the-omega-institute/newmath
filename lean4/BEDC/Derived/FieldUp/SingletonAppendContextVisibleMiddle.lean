import BEDC.Derived.FieldUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonClassifier_append_context_visible_middle_absurd {L R p q S : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R ->
      (FieldSingletonClassifier (append L (BHist.e0 p)) (append R S) -> False) ∧
        (FieldSingletonClassifier (append L (BHist.e1 p)) (append R S) -> False) ∧
          (FieldSingletonClassifier (append L S) (append R (BHist.e0 q)) -> False) ∧
            (FieldSingletonClassifier (append L S) (append R (BHist.e1 q)) -> False) := by
  intro carrierL carrierR
  constructor
  · intro classified
    have exposed : FieldSingletonClassifier (BHist.e0 p) S :=
      (FieldSingletonClassifier_append_context_cancel_iff carrierL carrierR).mp classified
    exact (FieldSingletonClassifier_visible_endpoint_absurd (p := p) (q := p) (k := S)).left
      exposed
  · constructor
    · intro classified
      have exposed : FieldSingletonClassifier (BHist.e1 p) S :=
        (FieldSingletonClassifier_append_context_cancel_iff carrierL carrierR).mp classified
      exact (FieldSingletonClassifier_visible_endpoint_absurd (p := p) (q := p) (k := S)).right.left
        exposed
    · constructor
      · intro classified
        have exposed : FieldSingletonClassifier S (BHist.e0 q) :=
          (FieldSingletonClassifier_append_context_cancel_iff carrierL carrierR).mp classified
        exact (FieldSingletonClassifier_visible_endpoint_absurd (p := q) (q := q) (k := S)).right.right.left
          exposed
      · intro classified
        have exposed : FieldSingletonClassifier S (BHist.e1 q) :=
          (FieldSingletonClassifier_append_context_cancel_iff carrierL carrierR).mp classified
        exact (FieldSingletonClassifier_visible_endpoint_absurd (p := q) (q := q) (k := S)).right.right.right
          exposed

end BEDC.Derived.FieldUp
