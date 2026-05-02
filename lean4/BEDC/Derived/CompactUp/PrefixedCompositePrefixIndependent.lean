import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CompactNetWitness_prefixed_composite_prefix_independent_result_deterministic
    {p p' center precision extra composite refined refined' : BHist} :
    UnaryHistory precision -> UnaryHistory extra -> Cont precision extra composite ->
      CompactNetWitness (append p center) composite (append p refined) ->
        CompactNetWitness (append p' center) composite (append p' refined') ->
          hsame refined refined' := by
  intro precisionCarrier extraCarrier compositeRel left right
  have leftFactor :=
    CompactNetWitness_prefixed_composite_factorizes precisionCarrier extraCarrier compositeRel left
  have rightFactor :=
    CompactNetWitness_prefixed_composite_factorizes precisionCarrier extraCarrier compositeRel right
  cases leftFactor with
  | intro net leftData =>
      cases rightFactor with
      | intro net' rightData =>
          exact
            CompactNetWitness_composite_result_deterministic leftData.left leftData.right
              rightData.left rightData.right

end BEDC.Derived.CompactUp
