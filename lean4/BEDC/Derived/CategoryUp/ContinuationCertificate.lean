import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert

theorem ContinuationMorphism_tail_semanticNameCert {a b : BHist}
    (m : ContinuationMorphism a b) :
    SemanticNameCert (fun t : BHist => Cont a t b)
      (fun t : BHist => Cont a t b) (fun t : BHist => Cont a t b) hsame := by
  constructor
  · constructor
    · exact Exists.intro m.tail m.rel
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      cases same
      exact carrier
  · intro h source
    exact source
  · intro h source
    exact source

theorem ContinuationMorphism_endpoint_transport_tail_classified {a a' b b' : BHist}
    (sameSource : hsame a a') (sameTarget : hsame b b')
    (left : ContinuationMorphism a b) (right : ContinuationMorphism a' b') :
    Cont a' left.tail b' ∧ hsame left.tail right.tail := by
  have transported := cont_hsame_transport sameSource (hsame_refl left.tail) sameTarget left.rel
  exact And.intro transported (cont_left_cancel transported right.rel)

theorem CategoryHomCarrier_continuation_morphism_tail_iff {a b f : BHist} :
    CategoryHomCarrier a b f <->
      UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory f ∧
        Exists (fun m : ContinuationMorphism a b => hsame m.tail f) := by
  constructor
  · intro homCarrier
    exact And.intro homCarrier.left
      (And.intro homCarrier.right.left
        (And.intro homCarrier.right.right.left
          (Exists.intro { tail := f, rel := homCarrier.right.right.right } (hsame_refl f))))
  · intro data
    cases data with
    | intro sourceCarrier rest =>
        cases rest with
        | intro targetCarrier rest =>
            cases rest with
            | intro tailCarrier witness =>
                cases witness with
                | intro m sameTail =>
                    exact And.intro sourceCarrier
                      (And.intro targetCarrier
                        (And.intro tailCarrier
                          (cont_hsame_transport (hsame_refl a) sameTail (hsame_refl b)
                            m.rel)))

end BEDC.Derived.CategoryUp
