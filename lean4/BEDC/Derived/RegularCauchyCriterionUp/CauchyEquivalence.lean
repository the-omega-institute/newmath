import BEDC.Derived.RegularCauchyCriterionUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RegularCauchyCriterionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

private theorem RegularCauchyCriterionCauchyEquivalence_encode_append_aux
    (left right : BHist) :
    regularCauchyCriterionEncodeBHist (append left right) =
      List.append (regularCauchyCriterionEncodeBHist right)
        (regularCauchyCriterionEncodeBHist left) := by
  -- BEDC touchpoint anchor: BHist BMark append
  induction right with
  | Empty =>
      rfl
  | e0 right ih =>
      exact congrArg (fun tail => BMark.b0 :: tail) ih
  | e1 right ih =>
      exact congrArg (fun tail => BMark.b1 :: tail) ih

theorem RegularCauchyCriterionCauchyEquivalence_encode_append (Q V A : BHist) :
    regularCauchyCriterionEncodeBHist (append (append Q V) A) =
      List.append (regularCauchyCriterionEncodeBHist A)
        (List.append (regularCauchyCriterionEncodeBHist V)
          (regularCauchyCriterionEncodeBHist Q)) := by
  -- BEDC touchpoint anchor: BHist BMark append
  rw [RegularCauchyCriterionCauchyEquivalence_encode_append_aux (append Q V) A,
    RegularCauchyCriterionCauchyEquivalence_encode_append_aux Q V]

end BEDC.Derived.RegularCauchyCriterionUp
