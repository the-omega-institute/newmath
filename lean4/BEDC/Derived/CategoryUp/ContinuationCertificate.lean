import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

end BEDC.Derived.CategoryUp
