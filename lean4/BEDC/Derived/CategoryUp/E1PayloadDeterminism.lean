import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist

theorem CategoryHomCarrier_e1_source_e1_target_morphism_payload_deterministic
    {a a' r r' k k' : BHist} :
    hsame a a' -> hsame r r' -> CategoryHomCarrier (BHist.e1 a) (BHist.e1 r) (BHist.e1 k) ->
      CategoryHomCarrier (BHist.e1 a') (BHist.e1 r') (BHist.e1 k') -> hsame k k' := by
  intro sameSource sameTarget left right
  exact hsame_e1_iff.mp
    (CategoryHomCarrier_endpoint_hsame_morphism_deterministic
      (hsame_e1_iff.mpr sameSource) (hsame_e1_iff.mpr sameTarget) left right)

end BEDC.Derived.CategoryUp
