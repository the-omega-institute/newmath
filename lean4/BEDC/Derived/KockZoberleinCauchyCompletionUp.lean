import BEDC.FKernel.Unary.History

namespace BEDC.Derived.KockZoberleinCauchyCompletionUp

open BEDC.FKernel.Hist

inductive KockZoberleinCauchyCompletionUp : Type where
  | mk :
      (doctrine completion join idempotence yoneda lawvere stream regular dyadic real
        handoff transport replay provenance localName : BHist) →
      KockZoberleinCauchyCompletionUp

end BEDC.Derived.KockZoberleinCauchyCompletionUp
