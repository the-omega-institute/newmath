import BEDC.Derived.FunctorUp
import BEDC.Derived.CategoryUp.MorphismEmptyEndpoint

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_morphism_empty_endpoint_iff {p a b f : BHist} :
    CategoryHomCarrier (append p a) (append p b) f -> (hsame f BHist.Empty <-> hsame a b) := by
  intro homCarrier
  constructor
  · intro morphismEmpty
    have sameEndpoints :
        hsame (append p a) (append p b) :=
      (CategoryHomCarrier_morphism_empty_endpoint_iff homCarrier).mp morphismEmpty
    exact append_left_cancel (h := p) sameEndpoints
  · intro sameEndpoints
    have samePrefixed : hsame (append p a) (append p b) := by
      cases sameEndpoints
      rfl
    exact (CategoryHomCarrier_morphism_empty_endpoint_iff homCarrier).mpr samePrefixed

theorem FunctorPrefixHomCarrier_comp_result_empty_iff {p a b c f g fg : BHist} :
    CategoryHomCarrier (append p a) (append p b) f ->
      CategoryHomCarrier (append p b) (append p c) g -> Cont f g fg ->
        (hsame fg BHist.Empty <->
          hsame f BHist.Empty ∧ hsame g BHist.Empty ∧ hsame a b ∧ hsame b c) := by
  intro left right comp
  constructor
  · intro resultEmpty
    have emptyComp : Cont f g BHist.Empty :=
      cont_result_hsame_transport comp resultEmpty
    exact (FunctorPrefixHomCarrier_comp_empty_iff left right).mp emptyComp
  · intro emptyData
    have emptyComp : Cont f g BHist.Empty :=
      (FunctorPrefixHomCarrier_comp_empty_iff left right).mpr emptyData
    exact cont_deterministic comp emptyComp

theorem FunctorPrefixHomCarrier_empty_target_source_morphism_swap_iff {p a f : BHist} :
    CategoryHomCarrier (append p a) BHist.Empty f ↔
      CategoryHomCarrier f BHist.Empty (append p a) := by
  constructor
  · intro homCarrier
    have data :=
      (CategoryHomCarrier_empty_target_iff (a := append p a) (f := f)).mp homCarrier
    exact (CategoryHomCarrier_empty_target_iff (a := f) (f := append p a)).mpr
      (And.intro data.right data.left)
  · intro homCarrier
    have data :=
      (CategoryHomCarrier_empty_target_iff (a := f) (f := append p a)).mp homCarrier
    exact (CategoryHomCarrier_empty_target_iff (a := append p a) (f := f)).mpr
      (And.intro data.right data.left)

end BEDC.Derived.FunctorUp
