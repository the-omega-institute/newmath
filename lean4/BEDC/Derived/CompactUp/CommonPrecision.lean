import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CompactNetWitness_common_precision_center_transport
    {center center' precision net net' : BHist} :
    CompactNetWitness center precision net -> CompactNetWitness center' precision net' ->
      hsame net net' -> Cont center' precision net ∧ hsame center center' := by
  intro left right sameNet
  exact And.intro
    (cont_result_hsame_transport right.right.right.right (hsame_symm sameNet))
    (cont_common_suffix_cancellation left.right.right.right right.right.right.right sameNet)

theorem CompactNetWitness_common_center_precision_transport
    {center precision precision' net net' : BHist} :
    CompactNetWitness center precision net -> CompactNetWitness center precision' net' ->
      hsame net net' -> Cont center precision' net ∧ hsame precision precision' := by
  intro left right sameNet
  exact And.intro
    (cont_result_hsame_transport right.right.right.right (hsame_symm sameNet))
    (CompactNetWitness_precision_hsame_deterministic (hsame_refl center) sameNet left right)

end BEDC.Derived.CompactUp
