import BEDC.Derived.FiniteTailFilterUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteTailFilterUp : Type where
  | mk :
      (streamWindow dyadicTolerance regularReadback tailBudget commonTail realSeal handoff
        consumer provenance nameCert : BHist) →
        FiniteTailFilterUp

def finiteTailFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteTailFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteTailFilterEncodeBHist h

def finiteTailFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteTailFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteTailFilterDecodeBHist tail)

private theorem finiteTailFilter_decode_encode :
    ∀ h : BHist, finiteTailFilterDecodeBHist (finiteTailFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteTailFilterFields : FiniteTailFilterUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | FiniteTailFilterUp.mk streamWindow dyadicTolerance regularReadback tailBudget commonTail
      realSeal handoff consumer provenance nameCert =>
      [streamWindow, dyadicTolerance, regularReadback, tailBudget, commonTail, realSeal,
        handoff, consumer, provenance, nameCert]

def finiteTailFilterToEventFlow : FiniteTailFilterUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteTailFilterFields x).map finiteTailFilterEncodeBHist

def finiteTailFilterFromEventFlow : EventFlow → Option FiniteTailFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    match ef with
    | streamWindow :: rest1 =>
        match rest1 with
        | dyadicTolerance :: rest2 =>
            match rest2 with
            | regularReadback :: rest3 =>
                match rest3 with
                | tailBudget :: rest4 =>
                    match rest4 with
                    | commonTail :: rest5 =>
                        match rest5 with
                        | realSeal :: rest6 =>
                            match rest6 with
                            | handoff :: rest7 =>
                                match rest7 with
                                | consumer :: rest8 =>
                                    match rest8 with
                                    | provenance :: rest9 =>
                                        match rest9 with
                                        | nameCert :: rest10 =>
                                            match rest10 with
                                            | [] =>
                                                some
                                                  (FiniteTailFilterUp.mk
                                                    (finiteTailFilterDecodeBHist streamWindow)
                                                    (finiteTailFilterDecodeBHist dyadicTolerance)
                                                    (finiteTailFilterDecodeBHist regularReadback)
                                                    (finiteTailFilterDecodeBHist tailBudget)
                                                    (finiteTailFilterDecodeBHist commonTail)
                                                    (finiteTailFilterDecodeBHist realSeal)
                                                    (finiteTailFilterDecodeBHist handoff)
                                                    (finiteTailFilterDecodeBHist consumer)
                                                    (finiteTailFilterDecodeBHist provenance)
                                                    (finiteTailFilterDecodeBHist nameCert))
                                            | _ :: _ => none
                                        | [] => none
                                    | [] => none
                                | [] => none
                            | [] => none
                        | [] => none
                    | [] => none
                | [] => none
            | [] => none
        | [] => none
    | [] => none

private theorem finiteTailFilter_round_trip :
    ∀ x : FiniteTailFilterUp,
      finiteTailFilterFromEventFlow (finiteTailFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk streamWindow dyadicTolerance regularReadback tailBudget commonTail realSeal handoff
      consumer provenance nameCert =>
      change
        some
            (FiniteTailFilterUp.mk
              (finiteTailFilterDecodeBHist (finiteTailFilterEncodeBHist streamWindow))
              (finiteTailFilterDecodeBHist (finiteTailFilterEncodeBHist dyadicTolerance))
              (finiteTailFilterDecodeBHist (finiteTailFilterEncodeBHist regularReadback))
              (finiteTailFilterDecodeBHist (finiteTailFilterEncodeBHist tailBudget))
              (finiteTailFilterDecodeBHist (finiteTailFilterEncodeBHist commonTail))
              (finiteTailFilterDecodeBHist (finiteTailFilterEncodeBHist realSeal))
              (finiteTailFilterDecodeBHist (finiteTailFilterEncodeBHist handoff))
              (finiteTailFilterDecodeBHist (finiteTailFilterEncodeBHist consumer))
              (finiteTailFilterDecodeBHist (finiteTailFilterEncodeBHist provenance))
              (finiteTailFilterDecodeBHist (finiteTailFilterEncodeBHist nameCert))) =
          some
            (FiniteTailFilterUp.mk streamWindow dyadicTolerance regularReadback tailBudget
              commonTail realSeal handoff consumer provenance nameCert)
      rw [finiteTailFilter_decode_encode streamWindow]
      rw [finiteTailFilter_decode_encode dyadicTolerance]
      rw [finiteTailFilter_decode_encode regularReadback]
      rw [finiteTailFilter_decode_encode tailBudget]
      rw [finiteTailFilter_decode_encode commonTail]
      rw [finiteTailFilter_decode_encode realSeal]
      rw [finiteTailFilter_decode_encode handoff]
      rw [finiteTailFilter_decode_encode consumer]
      rw [finiteTailFilter_decode_encode provenance]
      rw [finiteTailFilter_decode_encode nameCert]

private theorem finiteTailFilterToEventFlow_injective {x y : FiniteTailFilterUp} :
    finiteTailFilterToEventFlow x = finiteTailFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = finiteTailFilterFromEventFlow (finiteTailFilterToEventFlow x) :=
        (finiteTailFilter_round_trip x).symm
      _ = finiteTailFilterFromEventFlow (finiteTailFilterToEventFlow y) :=
        congrArg finiteTailFilterFromEventFlow hxy
      _ = some y := finiteTailFilter_round_trip y
  exact Option.some.inj optionEq

instance finiteTailFilterBHistCarrier : BHistCarrier FiniteTailFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteTailFilterToEventFlow
  fromEventFlow := finiteTailFilterFromEventFlow

instance finiteTailFilterChapterTasteGate : ChapterTasteGate FiniteTailFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteTailFilterFromEventFlow (finiteTailFilterToEventFlow x) = some x
    exact finiteTailFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteTailFilterToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FiniteTailFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteTailFilterChapterTasteGate

theorem finiteTailFilterTasteGate_single_carrier_alignment :
    (∀ x : FiniteTailFilterUp,
      finiteTailFilterFromEventFlow (finiteTailFilterToEventFlow x) = some x) ∧
    (∀ {x y : FiniteTailFilterUp},
      finiteTailFilterToEventFlow x = finiteTailFilterToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact finiteTailFilter_round_trip
  · intro x y hxy
    exact finiteTailFilterToEventFlow_injective hxy

end BEDC.Derived.FiniteTailFilterUp
