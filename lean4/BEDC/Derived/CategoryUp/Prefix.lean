import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_unary_prefix_iff {p a b f : BHist} :
    CategoryHomCarrier (append p a) (append p b) f <-> UnaryHistory p ∧
      CategoryHomCarrier a b f := by
  constructor
  · intro homCarrier
    cases homCarrier with
    | intro sourceCarrier homRest =>
        cases homRest with
        | intro targetCarrier homRest =>
            cases homRest with
            | intro morphismCarrier homCont =>
                exact
                  And.intro
                    (unary_append_left_factor sourceCarrier)
                    (And.intro
                      (unary_append_right_factor sourceCarrier)
                      (And.intro
                        (unary_append_right_factor targetCarrier)
                        (And.intro morphismCarrier (cont_prefix_cancel homCont))))
  · intro prefixed
    cases prefixed with
    | intro prefixCarrier homCarrier =>
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
                          (unary_append_closed prefixCarrier targetCarrier)
                          (And.intro morphismCarrier
                            (cont_intro (append_assoc p a f).symm)))

theorem CategoryHomCarrier_unary_prefix_comp_public_readback {p a b c f g fg : BHist} :
    UnaryHistory p -> CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier (append p a) (append p c) fg ∧
        (forall {fg' : BHist}, CategoryHomCarrier (append p a) (append p c) fg' ->
          hsame fg fg') := by
  intro prefixCarrier left right comp
  have readback := CategoryHomCarrier_comp_public_readback left right comp
  constructor
  · exact CategoryHomCarrier_unary_prefix_iff.mpr (And.intro prefixCarrier readback.left)
  · intro fg' displayed
    exact readback.right (CategoryHomCarrier_unary_prefix_iff.mp displayed).right

theorem CategoryHomCarrier_unary_context_iff {p q a b f : BHist} :
    CategoryHomCarrier (append (append p a) q) (append (append p b) q) f ↔
      UnaryHistory p ∧ UnaryHistory q ∧ CategoryHomCarrier a b f := by
  constructor
  · intro homCarrier
    have suffixed :=
      (CategoryHomCarrier_unary_suffix_iff
        (q := q) (a := append p a) (b := append p b) (f := f)).mp homCarrier
    have prefixed := suffixed.right
    exact
      And.intro (unary_append_left_factor prefixed.left)
        (And.intro suffixed.left
          (And.intro (unary_append_right_factor prefixed.left)
            (And.intro (unary_append_right_factor prefixed.right.left)
              (And.intro prefixed.right.right.left
                (cont_prefix_cancel prefixed.right.right.right)))))
  · intro contextual
    cases contextual with
    | intro prefixCarrier rest =>
        cases rest with
        | intro suffixCarrier baseCarrier =>
            have prefixed : CategoryHomCarrier (append p a) (append p b) f := by
              cases baseCarrier with
              | intro sourceCarrier baseRest =>
                  cases baseRest with
                  | intro targetCarrier baseRest =>
                      cases baseRest with
                      | intro morphismCarrier baseCont =>
                          cases baseCont
                          exact
                            And.intro (unary_append_closed prefixCarrier sourceCarrier)
                              (And.intro (unary_append_closed prefixCarrier targetCarrier)
                                (And.intro morphismCarrier
                                  (cont_intro (append_assoc p a f).symm)))
            exact
              (CategoryHomCarrier_unary_suffix_iff
                (q := q) (a := append p a) (b := append p b) (f := f)).mpr
                (And.intro suffixCarrier prefixed)

end BEDC.Derived.CategoryUp
