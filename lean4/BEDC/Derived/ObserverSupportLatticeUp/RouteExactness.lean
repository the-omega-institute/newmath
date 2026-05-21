import BEDC.Derived.ObserverSupportLatticeUp.TasteGate

namespace BEDC.Derived.ObserverSupportLatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

theorem ObserverSupportLatticeCarrier_route_exactness {flow : EventFlow}
    {F S C B R H Q P N : BHist}
    (hflow :
      observerSupportLatticeFromEventFlow flow =
        some (ObserverSupportLatticeUp.mk F S C B R H Q P N)) :
    ∃ (eF eS eC eB eR eH eQ eP eN : List BMark),
      flow = eF :: eS :: eC :: eB :: eR :: eH :: eQ :: eP :: eN :: [] ∧
        observerSupportLatticeDecodeBHist eF = F ∧
          observerSupportLatticeDecodeBHist eS = S ∧
            observerSupportLatticeDecodeBHist eC = C ∧
              observerSupportLatticeDecodeBHist eB = B ∧
                observerSupportLatticeDecodeBHist eR = R ∧
                  observerSupportLatticeDecodeBHist eH = H ∧
                    observerSupportLatticeDecodeBHist eQ = Q ∧
                      observerSupportLatticeDecodeBHist eP = P ∧
                        observerSupportLatticeDecodeBHist eN = N := by
  -- BEDC touchpoint anchor: BHist BMark EventFlow
  cases flow with
  | nil =>
      cases hflow
  | cons eF rest0 =>
      cases rest0 with
      | nil =>
          cases hflow
      | cons eS rest1 =>
          cases rest1 with
          | nil =>
              cases hflow
          | cons eC rest2 =>
              cases rest2 with
              | nil =>
                  cases hflow
              | cons eB rest3 =>
                  cases rest3 with
                  | nil =>
                      cases hflow
                  | cons eR rest4 =>
                      cases rest4 with
                      | nil =>
                          cases hflow
                      | cons eH rest5 =>
                          cases rest5 with
                          | nil =>
                              cases hflow
                          | cons eQ rest6 =>
                              cases rest6 with
                              | nil =>
                                  cases hflow
                              | cons eP rest7 =>
                                  cases rest7 with
                                  | nil =>
                                      cases hflow
                                  | cons eN rest8 =>
                                      cases rest8 with
                                      | nil =>
                                          cases hflow
                                          exact
                                            ⟨eF, eS, eC, eB, eR, eH, eQ, eP, eN,
                                              rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                                              rfl, rfl, rfl⟩
                                      | cons _ _ =>
                                          cases hflow

end BEDC.Derived.ObserverSupportLatticeUp
