import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.LimitSelectorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

structure LimitSelectorCarrier : Type where
  regSeq : BHist
  precision : BHist
  modulus : BHist
  selectedIndex : BHist
  window : BHist
  dyadicReadback : BHist
  realSeal : BHist
  transports : BHist
  route : BHist
  provenance : BHist
  name : BHist
  selected_index_route : Cont precision modulus selectedIndex
  window_readback_route : Cont selectedIndex window dyadicReadback
  seal_route : Cont dyadicReadback realSeal route

theorem LimitSelectorCarrier_finite_witness_route (L : LimitSelectorCarrier) :
    Cont L.precision L.modulus L.selectedIndex ∧
      Cont L.selectedIndex L.window L.dyadicReadback ∧
        Cont L.dyadicReadback L.realSeal L.route := by
  exact ⟨L.selected_index_route, L.window_readback_route, L.seal_route⟩

theorem LimitSelectorCarrier_shared_budget_real_seal_determinacy
    (L : LimitSelectorCarrier) {sharedSeal alternateSeal : BHist}
    (sharedRoute : Cont L.dyadicReadback L.realSeal sharedSeal)
    (alternateRoute : Cont L.dyadicReadback L.realSeal alternateSeal) :
    hsame sharedSeal alternateSeal ∧ Cont L.dyadicReadback L.realSeal sharedSeal ∧
      Cont L.dyadicReadback L.realSeal alternateSeal ∧
        Cont L.precision L.modulus L.selectedIndex ∧
          Cont L.selectedIndex L.window L.dyadicReadback := by
  exact
    ⟨cont_deterministic sharedRoute alternateRoute, sharedRoute, alternateRoute,
      L.selected_index_route, L.window_readback_route⟩

theorem LimitSelectorCarrier_real_seal_nonescape
    (L : LimitSelectorCarrier) {selected readback : BHist}
    (hsel : Cont L.precision L.modulus selected)
    (hread : Cont selected L.window readback) :
    hsame selected L.selectedIndex ∧ hsame readback L.dyadicReadback := by
  have sameSelected : hsame selected L.selectedIndex :=
    cont_deterministic hsel L.selected_index_route
  have sameReadback : hsame readback L.dyadicReadback :=
    cont_respects_hsame sameSelected (hsame_refl L.window) hread L.window_readback_route
  exact ⟨sameSelected, sameReadback⟩

theorem LimitSelectorCarrier_diagonal_consumer_exhaustion
    (L : LimitSelectorCarrier) {selected readback sealConsumer downstreamConsumer : BHist}
    (hsel : Cont L.precision L.modulus selected)
    (hread : Cont selected L.window readback)
    (hseal : Cont readback L.realSeal sealConsumer)
    (hdown : Cont sealConsumer L.provenance downstreamConsumer) :
    hsame selected L.selectedIndex ∧ hsame readback L.dyadicReadback ∧
      hsame sealConsumer L.route ∧ Cont sealConsumer L.provenance downstreamConsumer ∧
        Cont L.precision L.modulus L.selectedIndex ∧
          Cont L.selectedIndex L.window L.dyadicReadback := by
  have sameSelected : hsame selected L.selectedIndex :=
    cont_deterministic hsel L.selected_index_route
  have sameReadback : hsame readback L.dyadicReadback :=
    cont_respects_hsame sameSelected (hsame_refl L.window) hread L.window_readback_route
  have sameSeal : hsame sealConsumer L.route :=
    cont_respects_hsame sameReadback (hsame_refl L.realSeal) hseal L.seal_route
  exact
    ⟨sameSelected, sameReadback, sameSeal, hdown, L.selected_index_route,
      L.window_readback_route⟩

end BEDC.Derived.LimitSelectorUp
