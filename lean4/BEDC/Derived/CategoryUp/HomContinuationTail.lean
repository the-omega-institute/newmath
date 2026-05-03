import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_continuationMorphism_tail_iff {a b f : BHist} :
    CategoryHomCarrier a b f ↔
      UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory f ∧
        ∃ m : ContinuationMorphism a b, hsame m.tail f := by
  constructor
  · intro homCarrier
    exact And.intro homCarrier.left
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
                    cases m with
                    | mk tail rel =>
                        cases sameTail
                        exact And.intro sourceCarrier
                          (And.intro targetCarrier (And.intro morphCarrier rel))

end BEDC.Derived.CategoryUp
