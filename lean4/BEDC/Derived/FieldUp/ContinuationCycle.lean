import BEDC.FKernel.Cont.Cancellation
import BEDC.Derived.FieldUp.SingletonEmpty
import BEDC.Derived.FieldUp.ProductApartness

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem fieldSingletonEmptyNonZero_continuation_cycle_tail_absurd {h k tail backTail : BHist} :
    Cont h tail k -> Cont k backTail h -> fieldSingletonEmptyNonZero tail -> False := by
  intro forward back nonzeroTail
  have tailEmpty : hsame tail BHist.Empty :=
    (cont_mutual_extension_tails_empty forward back).left
  exact fieldSingletonEmptyNonZero_empty_endpoint_absurd tailEmpty nonzeroTail

theorem FieldApartZero_mutual_continuation_cycle_tails_absurd {h k leftTail rightTail : BHist} :
    Cont h leftTail k -> Cont k rightTail h ->
      (FieldApartZero leftTail -> False) ∧ (FieldApartZero rightTail -> False) := by
  intro forward back
  have tailsEmpty := cont_mutual_extension_tails_empty forward back
  constructor
  · intro apartLeft
    exact apartLeft tailsEmpty.left
  · intro apartRight
    exact apartRight tailsEmpty.right

theorem FieldApartZero_triangle_continuation_cycle_tails_absurd {a b c f g h : BHist} :
    Cont a f b -> Cont b g c -> Cont c h a ->
      (FieldApartZero f -> False) ∧ (FieldApartZero g -> False) ∧
        (FieldApartZero h -> False) := by
  intro left middle back
  have tailsEmpty := cont_triangle_cycle_tails_empty left middle back
  constructor
  · intro apartF
    exact apartF tailsEmpty.left
  · constructor
    · intro apartG
      exact apartG tailsEmpty.right.left
    · intro apartH
      exact apartH tailsEmpty.right.right.left

end BEDC.Derived.FieldUp
