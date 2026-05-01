import BEDC.Derived.CategoryUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_preserves {p a b f : BHist} :
    UnaryHistory p -> CategoryHomCarrier a b f ->
      CategoryHomCarrier (append p a) (append p b) f := by
  intro prefixCarrier homCarrier
  cases homCarrier with
  | intro sourceCarrier homRest =>
      cases homRest with
      | intro targetCarrier homRest =>
          cases homRest with
          | intro morphismCarrier homCont =>
              cases homCont
              exact
                And.intro
                  (unary_append_closed prefixCarrier sourceCarrier)
                  (And.intro
                    (unary_append_closed prefixCarrier
                      (unary_cont_closed sourceCarrier morphismCarrier (cont_intro rfl)))
                    (And.intro morphismCarrier
                      (cont_intro (append_assoc p a f).symm)))

theorem FunctorPrefixHomCarrier_comp_preserves {p a b c f g fg : BHist} :
    UnaryHistory p -> CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier (append p a) (append p c) fg := by
  intro prefixCarrier left right comp
  exact
    FunctorPrefixHomCarrier_preserves prefixCarrier
      (CategoryHomCarrier_comp_closed left right comp)

end BEDC.Derived.FunctorUp
