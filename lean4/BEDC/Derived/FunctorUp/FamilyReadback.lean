import BEDC.Derived.FunctorUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_comp_family_public_readback {a b c f g fg displayed : BHist} :
    (forall {p : BHist}, UnaryHistory p -> CategoryHomCarrier (append p a) (append p b) f) ->
      (forall {p : BHist}, UnaryHistory p -> CategoryHomCarrier (append p b) (append p c) g) ->
        Cont f g fg ->
          (forall {p : BHist}, UnaryHistory p ->
            CategoryHomCarrier (append p a) (append p c) displayed) ->
            hsame fg displayed := by
  intro leftFamily rightFamily comp displayedFamily
  have leftEmpty :
      CategoryHomCarrier (append BHist.Empty a) (append BHist.Empty b) f :=
    leftFamily (p := BHist.Empty) unary_empty
  have rightEmpty :
      CategoryHomCarrier (append BHist.Empty b) (append BHist.Empty c) g :=
    rightFamily (p := BHist.Empty) unary_empty
  have displayedEmpty :
      CategoryHomCarrier (append BHist.Empty a) (append BHist.Empty c) displayed :=
    displayedFamily (p := BHist.Empty) unary_empty
  have compositeEmpty :
      CategoryHomCarrier (append BHist.Empty a) (append BHist.Empty c) fg :=
    CategoryHomCarrier_comp_closed leftEmpty rightEmpty comp
  exact CategoryHomCarrier_morphism_deterministic compositeEmpty displayedEmpty

end BEDC.Derived.FunctorUp
