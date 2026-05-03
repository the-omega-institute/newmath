import BEDC.Derived.CategoryUp.CompositeEmptyTail

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_comp_endpoint_cycle_tail_empty_iff {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    hsame a c <-> hsame (ContinuationMorphism_comp_closed left right).tail BHist.Empty := by
  constructor
  · exact ContinuationMorphism_comp_endpoint_cycle_tail_empty left right
  · intro tailEmpty
    have transported : Cont a BHist.Empty c :=
      cont_hsame_transport (hsame_refl a) tailEmpty (hsame_refl c)
        (ContinuationMorphism_comp_closed left right).rel
    exact hsame_symm (cont_deterministic transported (cont_right_unit a))

end BEDC.Derived.CategoryUp
