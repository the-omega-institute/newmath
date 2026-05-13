import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverCoordinateFrameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverCoordinateFrameUp : Type where
  | mk :
      (observerState localityCell multiHist causalReads bound transport routes provenance
        nameCert : BHist) →
      ObserverCoordinateFrameUp
  deriving DecidableEq

private def observerCoordinateFrameEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerCoordinateFrameEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerCoordinateFrameEncodeBHist h

private def observerCoordinateFrameDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerCoordinateFrameDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerCoordinateFrameDecodeBHist tail)

private theorem observerCoordinateFrameDecodeEncodeBHist :
    ∀ h : BHist,
      observerCoordinateFrameDecodeBHist (observerCoordinateFrameEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem observerCoordinateFrameMkCongr
    {observerState observerState' localityCell localityCell' multiHist multiHist'
      causalReads causalReads' bound bound' transport transport' routes routes'
      provenance provenance' nameCert nameCert' : BHist} :
    observerState = observerState' →
      localityCell = localityCell' →
        multiHist = multiHist' →
          causalReads = causalReads' →
            bound = bound' →
              transport = transport' →
                routes = routes' →
                  provenance = provenance' →
                    nameCert = nameCert' →
                      ObserverCoordinateFrameUp.mk observerState localityCell multiHist
                        causalReads bound transport routes provenance nameCert =
                        ObserverCoordinateFrameUp.mk observerState' localityCell' multiHist'
                          causalReads' bound' transport' routes' provenance' nameCert' := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hobserverState hlocalityCell hmultiHist hcausalReads hbound htransport hroutes
    hprovenance hnameCert
  cases hobserverState
  cases hlocalityCell
  cases hmultiHist
  cases hcausalReads
  cases hbound
  cases htransport
  cases hroutes
  cases hprovenance
  cases hnameCert
  rfl

private def observerCoordinateFrameToEventFlow : ObserverCoordinateFrameUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverCoordinateFrameUp.mk observerState localityCell multiHist causalReads bound transport
      routes provenance nameCert =>
      [observerCoordinateFrameEncodeBHist observerState,
        observerCoordinateFrameEncodeBHist localityCell,
        observerCoordinateFrameEncodeBHist multiHist,
        observerCoordinateFrameEncodeBHist causalReads,
        observerCoordinateFrameEncodeBHist bound,
        observerCoordinateFrameEncodeBHist transport,
        observerCoordinateFrameEncodeBHist routes,
        observerCoordinateFrameEncodeBHist provenance,
        observerCoordinateFrameEncodeBHist nameCert]

private def observerCoordinateFrameFromEventFlow :
    EventFlow → Option ObserverCoordinateFrameUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | observerState :: rest0 =>
      match rest0 with
      | [] => none
      | localityCell :: rest1 =>
          match rest1 with
          | [] => none
          | multiHist :: rest2 =>
              match rest2 with
              | [] => none
              | causalReads :: rest3 =>
                  match rest3 with
                  | [] => none
                  | bound :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | routes :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | nameCert :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (ObserverCoordinateFrameUp.mk
                                              (observerCoordinateFrameDecodeBHist observerState)
                                              (observerCoordinateFrameDecodeBHist localityCell)
                                              (observerCoordinateFrameDecodeBHist multiHist)
                                              (observerCoordinateFrameDecodeBHist causalReads)
                                              (observerCoordinateFrameDecodeBHist bound)
                                              (observerCoordinateFrameDecodeBHist transport)
                                              (observerCoordinateFrameDecodeBHist routes)
                                              (observerCoordinateFrameDecodeBHist provenance)
                                              (observerCoordinateFrameDecodeBHist nameCert))
                                      | _ :: _ => none

private theorem observerCoordinateFrame_round_trip :
    ∀ x : ObserverCoordinateFrameUp,
      observerCoordinateFrameFromEventFlow (observerCoordinateFrameToEventFlow x) = some x
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverCoordinateFrameUp.mk observerState localityCell multiHist causalReads bound transport
      routes provenance nameCert =>
      congrArg some
        (observerCoordinateFrameMkCongr
          (observerCoordinateFrameDecodeEncodeBHist observerState)
          (observerCoordinateFrameDecodeEncodeBHist localityCell)
          (observerCoordinateFrameDecodeEncodeBHist multiHist)
          (observerCoordinateFrameDecodeEncodeBHist causalReads)
          (observerCoordinateFrameDecodeEncodeBHist bound)
          (observerCoordinateFrameDecodeEncodeBHist transport)
          (observerCoordinateFrameDecodeEncodeBHist routes)
          (observerCoordinateFrameDecodeEncodeBHist provenance)
          (observerCoordinateFrameDecodeEncodeBHist nameCert))

private theorem observerCoordinateFrameToEventFlow_injective
    {x y : ObserverCoordinateFrameUp} :
    observerCoordinateFrameToEventFlow x = observerCoordinateFrameToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerCoordinateFrameFromEventFlow (observerCoordinateFrameToEventFlow x) =
        observerCoordinateFrameFromEventFlow (observerCoordinateFrameToEventFlow y) :=
    congrArg observerCoordinateFrameFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerCoordinateFrame_round_trip x).symm
      (Eq.trans hread (observerCoordinateFrame_round_trip y)))

instance observerCoordinateFrameBHistCarrier : BHistCarrier ObserverCoordinateFrameUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerCoordinateFrameToEventFlow
  fromEventFlow := observerCoordinateFrameFromEventFlow

instance observerCoordinateFrameChapterTasteGate :
    ChapterTasteGate ObserverCoordinateFrameUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      observerCoordinateFrameFromEventFlow (observerCoordinateFrameToEventFlow x) = some x
    exact observerCoordinateFrame_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerCoordinateFrameToEventFlow_injective heq)

theorem ObserverCoordinateFrameUp_taste_gate_boundary :
    (∀ h : BHist,
      observerCoordinateFrameDecodeBHist (observerCoordinateFrameEncodeBHist h) = h) ∧
      (∀ x : ObserverCoordinateFrameUp,
        observerCoordinateFrameFromEventFlow (observerCoordinateFrameToEventFlow x) = some x) ∧
        (∀ x y : ObserverCoordinateFrameUp,
          observerCoordinateFrameToEventFlow x = observerCoordinateFrameToEventFlow y → x = y) ∧
          ∃ x : ObserverCoordinateFrameUp,
            x =
                ObserverCoordinateFrameUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
              observerCoordinateFrameFromEventFlow (observerCoordinateFrameToEventFlow x) =
                some x := by
  -- BEDC touchpoint anchor: BHist BMark
  let x : ObserverCoordinateFrameUp :=
    ObserverCoordinateFrameUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  constructor
  · exact observerCoordinateFrameDecodeEncodeBHist
  · constructor
    · exact observerCoordinateFrame_round_trip
    · constructor
      · intro left right heq
        exact observerCoordinateFrameToEventFlow_injective heq
      · exact ⟨x, rfl, observerCoordinateFrame_round_trip x⟩

end BEDC.Derived.ObserverCoordinateFrameUp
