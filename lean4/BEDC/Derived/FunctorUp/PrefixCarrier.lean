import BEDC.Derived.FunctorUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

structure PrefixFunctorCarrier (p : BHist) : Prop where
  prefix_unary : UnaryHistory p
  hom_preserves : forall {a b f : BHist},
    CategoryHomCarrier a b f -> CategoryHomCarrier (append p a) (append p b) f
  hom_reflects : forall {a b f : BHist},
    CategoryHomCarrier (append p a) (append p b) f -> CategoryHomCarrier a b f
  comp_preserves : forall {a b c f g fg : BHist},
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier (append p a) (append p c) fg

protected theorem PrefixFunctorCarrier_from_unary_prefix {p : BHist} :
    UnaryHistory p -> PrefixFunctorCarrier p := by
  intro prefixCarrier
  constructor
  · exact prefixCarrier
  · intro _a _b _f homCarrier
    exact FunctorPrefixHomCarrier_preserves prefixCarrier homCarrier
  · intro _a _b _f prefixedCarrier
    exact FunctorPrefixHomCarrier_reflects prefixedCarrier
  · intro _a _b _c _f _g _fg left right comp
    exact FunctorPrefixHomCarrier_comp_preserves prefixCarrier left right comp

end BEDC.Derived.FunctorUp
