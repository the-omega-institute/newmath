import BEDC.FKernel.Cont.Cancellation
import BEDC.Derived.FieldUp.SingletonEmpty

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem fieldSingletonEmptyNonZero_continuation_cycle_tail_absurd {h k tail backTail : BHist} :
    Cont h tail k -> Cont k backTail h -> fieldSingletonEmptyNonZero tail -> False := by
  intro forward back nonzeroTail
  have tailEmpty : hsame tail BHist.Empty :=
    (cont_mutual_extension_tails_empty forward back).left
  exact fieldSingletonEmptyNonZero_empty_endpoint_absurd tailEmpty nonzeroTail

end BEDC.Derived.FieldUp
