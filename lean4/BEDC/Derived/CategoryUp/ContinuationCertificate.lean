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

end BEDC.Derived.CategoryUp
