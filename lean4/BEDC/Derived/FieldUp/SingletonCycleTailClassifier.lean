import BEDC.Derived.FieldUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonClassifier_mutual_continuation_cycle_tails {h k tail backTail : BHist} :
    Cont h tail k -> Cont k backTail h -> FieldSingletonClassifier tail backTail := by
  intro forward back
  have tailsEmpty := cont_mutual_extension_tails_empty forward back
  exact And.intro tailsEmpty.left
    (And.intro tailsEmpty.right (hsame_trans tailsEmpty.left (hsame_symm tailsEmpty.right)))

end BEDC.Derived.FieldUp
