import BEDC.FKernel.Unary

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def CategoryHomCarrier (a b f : BHist) : Prop :=
  UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory f ∧ Cont a f b

theorem CategoryHomCarrier_comp_closed {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier a c fg := by
  intro left right comp
  cases left with
  | intro sourceCarrier leftRest =>
      cases leftRest with
      | intro _middleCarrier leftHomRest =>
          cases leftHomRest with
          | intro fCarrier leftCont =>
              cases right with
              | intro middleCarrier rightRest =>
                  cases rightRest with
                  | intro targetCarrier rightHomRest =>
                      cases rightHomRest with
                      | intro gCarrier rightCont =>
                          cases leftCont
                          cases rightCont
                          cases comp
                          exact
                            And.intro sourceCarrier
                              (And.intro targetCarrier
                                (And.intro
                                  (unary_cont_closed fCarrier gCarrier (cont_intro rfl))
                                  (cont_intro (append_assoc a f g))))

end BEDC.Derived.CategoryUp
