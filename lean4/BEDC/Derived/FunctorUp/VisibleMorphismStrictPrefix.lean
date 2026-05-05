import BEDC.Derived.FunctorUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp
open BEDC.Derived.NatUp

theorem FunctorPrefixHomCarrier_e1_visible_morphism_endpoint_hsame_absurd {p a r k : BHist} :
    CategoryHomCarrier (append p (BHist.e1 a)) (append p (BHist.e1 r)) (BHist.e1 k) ->
      (k = BHist.Empty -> False) -> hsame (BHist.e1 a) r -> False := by
  intro homCarrier tailNonempty sameEndpoint
  have strictPrefix :=
    FunctorPrefixHomCarrier_e1_visible_morphism_strict_prefix homCarrier tailNonempty
  cases strictPrefix with
  | intro tail data =>
      exact
        NatUnaryStrictPrefix_tail_endpoint_hsame_absurd
          data.left data.right.left data.right.right sameEndpoint

theorem FunctorPrefixHomCarrier_e1_visible_morphism_unique_strict_boundary
    {p a r k k' : BHist} :
    CategoryHomCarrier (append p (BHist.e1 a)) (append p (BHist.e1 r)) (BHist.e1 k) ->
      CategoryHomCarrier (append p (BHist.e1 a)) (append p (BHist.e1 r)) (BHist.e1 k') ->
        (k = BHist.Empty -> False) ->
          hsame k k' ∧ NatUnaryStrictPrefix (BHist.e1 a) r ∧
            (hsame (BHist.e1 a) r -> False) := by
  intro left right tailNonempty
  have sameDisplayed : hsame (BHist.e1 k) (BHist.e1 k') :=
    CategoryHomCarrier_morphism_deterministic left right
  have sameTail : hsame k k' := hsame_e1_iff.mp sameDisplayed
  have strictBoundary : NatUnaryStrictPrefix (BHist.e1 a) r :=
    FunctorPrefixHomCarrier_e1_visible_morphism_strict_prefix left tailNonempty
  have endpointAbsurd : hsame (BHist.e1 a) r -> False :=
    FunctorPrefixHomCarrier_e1_visible_morphism_endpoint_hsame_absurd left tailNonempty
  exact And.intro sameTail (And.intro strictBoundary endpointAbsurd)

theorem FunctorPrefixHomCarrier_e1_visible_morphism_payload_deterministic
    {p p' a a' r r' k k' : BHist} :
    hsame p p' -> hsame a a' -> hsame r r' ->
      CategoryHomCarrier (append p (BHist.e1 a)) (append p (BHist.e1 r)) (BHist.e1 k) ->
        CategoryHomCarrier (append p' (BHist.e1 a')) (append p' (BHist.e1 r'))
          (BHist.e1 k') ->
          hsame k k' := by
  intro samePrefix sameSource sameTarget left right
  cases samePrefix
  cases sameSource
  cases sameTarget
  exact hsame_e1_iff.mp (CategoryHomCarrier_morphism_deterministic left right)

end BEDC.Derived.FunctorUp
