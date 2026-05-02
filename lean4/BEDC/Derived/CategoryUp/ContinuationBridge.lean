import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_continuation_morphism_tail_correspondence {a b f : BHist} :
    CategoryHomCarrier a b f <->
      UnaryHistory a /\ UnaryHistory b /\ UnaryHistory f /\
        Exists (fun m : ContinuationMorphism a b => hsame m.tail f) := by
  constructor
  · intro homCarrier
    exact
      And.intro homCarrier.left
        (And.intro homCarrier.right.left
          (And.intro homCarrier.right.right.left
            (Exists.intro
              { tail := f, rel := homCarrier.right.right.right }
              (hsame_refl f))))
  · intro data
    cases data with
    | intro sourceCarrier rest =>
        cases rest with
        | intro targetCarrier rest =>
            cases rest with
            | intro morphCarrier witness =>
                cases witness with
                | intro m sameTail =>
                    exact
                      And.intro sourceCarrier
                        (And.intro targetCarrier
                          (And.intro morphCarrier
                            (cont_hsame_transport (hsame_refl a) sameTail
                              (hsame_refl b) m.rel)))

end BEDC.Derived.CategoryUp
