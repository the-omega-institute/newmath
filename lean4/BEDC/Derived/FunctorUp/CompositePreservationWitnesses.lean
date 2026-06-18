import BEDC.Derived.FunctorUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem FunctorCompositePreservationWitnesses {p a b c f g fg : BHist} :
    UnaryHistory p -> CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier (append p a) (append p c) fg ∧
        (forall {fg' : BHist}, Cont f g fg' ->
          CategoryHomCarrier (append p a) (append p c) fg' -> hsame fg fg') := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro prefixCarrier left right comp
  have compositeCarrier :
      CategoryHomCarrier (append p a) (append p c) fg :=
    FunctorPrefixHomCarrier_comp_preserves prefixCarrier left right comp
  constructor
  · exact compositeCarrier
  · intro fg' _comp' displayedCarrier
    exact CategoryHomCarrier_morphism_deterministic compositeCarrier displayedCarrier

end BEDC.Derived.FunctorUp
