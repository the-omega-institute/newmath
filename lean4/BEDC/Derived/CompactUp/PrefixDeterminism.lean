import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CompactNetWitness_prefixed_result_deterministic {p center precision net net' : BHist} :
    CompactNetWitness (append p center) precision (append p net) ->
      CompactNetWitness (append p center) precision (append p net') -> hsame net net' := by
  intro left right
  have samePrefixed : hsame (append p net) (append p net') :=
    cont_deterministic left.right.right.right right.right.right.right
  exact append_left_cancel (h := p) samePrefixed

end BEDC.Derived.CompactUp
