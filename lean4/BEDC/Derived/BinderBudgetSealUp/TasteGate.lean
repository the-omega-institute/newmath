import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BinderBudgetSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BinderBudgetSealUp : Type where
  | mk :
      (depth term payload shiftRoute substRoute transport contRoute provenance name : BHist) ->
      BinderBudgetSealUp
  deriving DecidableEq

def binderBudgetSealEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: binderBudgetSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: binderBudgetSealEncodeBHist h

def binderBudgetSealDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (binderBudgetSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (binderBudgetSealDecodeBHist tail)

private theorem binderBudgetSealDecode_encode_bhist :
    forall h : BHist, binderBudgetSealDecodeBHist (binderBudgetSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def binderBudgetSealToEventFlow : BinderBudgetSealUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BinderBudgetSealUp.mk depth term payload shiftRoute substRoute transport contRoute
      provenance name =>
      [[BMark.b0],
        binderBudgetSealEncodeBHist depth,
        [BMark.b1, BMark.b0],
        binderBudgetSealEncodeBHist term,
        [BMark.b1, BMark.b1, BMark.b0],
        binderBudgetSealEncodeBHist payload,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        binderBudgetSealEncodeBHist shiftRoute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        binderBudgetSealEncodeBHist substRoute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        binderBudgetSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        binderBudgetSealEncodeBHist contRoute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        binderBudgetSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        binderBudgetSealEncodeBHist name]

def binderBudgetSealFromEventFlow : EventFlow -> Option BinderBudgetSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | depth :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | term :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | payload :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | shiftRoute :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | substRoute :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | contRoute :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (BinderBudgetSealUp.mk
                                                                                  (binderBudgetSealDecodeBHist
                                                                                    depth)
                                                                                  (binderBudgetSealDecodeBHist
                                                                                    term)
                                                                                  (binderBudgetSealDecodeBHist
                                                                                    payload)
                                                                                  (binderBudgetSealDecodeBHist
                                                                                    shiftRoute)
                                                                                  (binderBudgetSealDecodeBHist
                                                                                    substRoute)
                                                                                  (binderBudgetSealDecodeBHist
                                                                                    transport)
                                                                                  (binderBudgetSealDecodeBHist
                                                                                    contRoute)
                                                                                  (binderBudgetSealDecodeBHist
                                                                                    provenance)
                                                                                  (binderBudgetSealDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem binderBudgetSeal_round_trip :
    forall x : BinderBudgetSealUp,
      binderBudgetSealFromEventFlow (binderBudgetSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk depth term payload shiftRoute substRoute transport contRoute provenance name =>
      change
        some
          (BinderBudgetSealUp.mk
            (binderBudgetSealDecodeBHist (binderBudgetSealEncodeBHist depth))
            (binderBudgetSealDecodeBHist (binderBudgetSealEncodeBHist term))
            (binderBudgetSealDecodeBHist (binderBudgetSealEncodeBHist payload))
            (binderBudgetSealDecodeBHist (binderBudgetSealEncodeBHist shiftRoute))
            (binderBudgetSealDecodeBHist (binderBudgetSealEncodeBHist substRoute))
            (binderBudgetSealDecodeBHist (binderBudgetSealEncodeBHist transport))
            (binderBudgetSealDecodeBHist (binderBudgetSealEncodeBHist contRoute))
            (binderBudgetSealDecodeBHist (binderBudgetSealEncodeBHist provenance))
            (binderBudgetSealDecodeBHist (binderBudgetSealEncodeBHist name))) =
          some
            (BinderBudgetSealUp.mk depth term payload shiftRoute substRoute transport contRoute
              provenance name)
      rw [binderBudgetSealDecode_encode_bhist depth,
        binderBudgetSealDecode_encode_bhist term,
        binderBudgetSealDecode_encode_bhist payload,
        binderBudgetSealDecode_encode_bhist shiftRoute,
        binderBudgetSealDecode_encode_bhist substRoute,
        binderBudgetSealDecode_encode_bhist transport,
        binderBudgetSealDecode_encode_bhist contRoute,
        binderBudgetSealDecode_encode_bhist provenance,
        binderBudgetSealDecode_encode_bhist name]

private theorem binderBudgetSealToEventFlow_injective {x y : BinderBudgetSealUp} :
    binderBudgetSealToEventFlow x = binderBudgetSealToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      binderBudgetSealFromEventFlow (binderBudgetSealToEventFlow x) =
        binderBudgetSealFromEventFlow (binderBudgetSealToEventFlow y) :=
    congrArg binderBudgetSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (binderBudgetSeal_round_trip x).symm
      (Eq.trans hread (binderBudgetSeal_round_trip y)))

instance binderBudgetSealBHistCarrier : BHistCarrier BinderBudgetSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := binderBudgetSealToEventFlow
  fromEventFlow := binderBudgetSealFromEventFlow

instance binderBudgetSealChapterTasteGate : ChapterTasteGate BinderBudgetSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change binderBudgetSealFromEventFlow (binderBudgetSealToEventFlow x) = some x
    exact binderBudgetSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (binderBudgetSealToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BinderBudgetSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  binderBudgetSealChapterTasteGate

theorem BinderBudgetSealTasteGate_single_carrier_alignment :
    (forall x : BinderBudgetSealUp,
      binderBudgetSealFromEventFlow (binderBudgetSealToEventFlow x) = some x) ∧
      (forall x y : BinderBudgetSealUp,
        binderBudgetSealToEventFlow x = binderBudgetSealToEventFlow y -> x = y) ∧
        (forall x : BinderBudgetSealUp, forall (w : RawEvent) (m : DisplayAlphabet),
          List.Mem w (binderBudgetSealToEventFlow x) ->
            List.Mem m w -> m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact binderBudgetSeal_round_trip
  · constructor
    · intro x y heq
      exact binderBudgetSealToEventFlow_injective heq
    · intro x w m hw hm
      exact event_flow_conservativity (S := binderBudgetSealToEventFlow x) hw hm

end BEDC.Derived.BinderBudgetSealUp
