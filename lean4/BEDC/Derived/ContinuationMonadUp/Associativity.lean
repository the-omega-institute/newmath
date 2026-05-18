import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ContinuationMonadCarrier_associativity
    {A B C f g u H K L N rightAssoc : BHist} :
    ContinuationMonadCarrier A B C f g u H K L N →
      Cont f (append g u) rightAssoc →
        hsame L rightAssoc ∧ Cont (append f g) u L ∧
          Cont f (append g u) rightAssoc := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier rightRoute
  obtain ⟨_unaryA, _unaryF, _unaryG, _unaryU, _routeB, _routeC, routeK, routeL,
    _sameEndpoint⟩ := carrier
  have leftRoute : Cont (append f g) u L := by
    cases routeK
    exact routeL
  have sameAssoc : hsame L rightAssoc := by
    cases routeK
    cases routeL
    cases rightRoute
    exact append_assoc f g u
  exact ⟨sameAssoc, leftRoute, rightRoute⟩

end BEDC.Derived.ContinuationMonadUp
