import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CountablyBasedUniformityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CountablyBasedUniformityUp : Type where
  | mk : (E F S Q D R H C P N : BHist) -> CountablyBasedUniformityUp

def countablyBasedUniformityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: countablyBasedUniformityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: countablyBasedUniformityEncodeBHist h

def countablyBasedUniformityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (countablyBasedUniformityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (countablyBasedUniformityDecodeBHist tail)

private theorem CountablyBasedUniformityTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      countablyBasedUniformityDecodeBHist (countablyBasedUniformityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def countablyBasedUniformityFields : CountablyBasedUniformityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CountablyBasedUniformityUp.mk E F S Q D R H C P N => [E, F, S, Q, D, R, H, C, P, N]

def countablyBasedUniformityToEventFlow : CountablyBasedUniformityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (countablyBasedUniformityFields x).map countablyBasedUniformityEncodeBHist

def countablyBasedUniformityFromEventFlow : EventFlow -> Option CountablyBasedUniformityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | E :: rest0 =>
      match rest0 with
      | [] => none
      | F :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | D :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CountablyBasedUniformityUp.mk
                                                  (countablyBasedUniformityDecodeBHist E)
                                                  (countablyBasedUniformityDecodeBHist F)
                                                  (countablyBasedUniformityDecodeBHist S)
                                                  (countablyBasedUniformityDecodeBHist Q)
                                                  (countablyBasedUniformityDecodeBHist D)
                                                  (countablyBasedUniformityDecodeBHist R)
                                                  (countablyBasedUniformityDecodeBHist H)
                                                  (countablyBasedUniformityDecodeBHist C)
                                                  (countablyBasedUniformityDecodeBHist P)
                                                  (countablyBasedUniformityDecodeBHist N))
                                          | _ :: _ => none

private theorem CountablyBasedUniformityTasteGate_single_carrier_alignment_round_trip :
    forall x : CountablyBasedUniformityUp,
      countablyBasedUniformityFromEventFlow (countablyBasedUniformityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E F S Q D R H C P N =>
      change
        some
          (CountablyBasedUniformityUp.mk
            (countablyBasedUniformityDecodeBHist (countablyBasedUniformityEncodeBHist E))
            (countablyBasedUniformityDecodeBHist (countablyBasedUniformityEncodeBHist F))
            (countablyBasedUniformityDecodeBHist (countablyBasedUniformityEncodeBHist S))
            (countablyBasedUniformityDecodeBHist (countablyBasedUniformityEncodeBHist Q))
            (countablyBasedUniformityDecodeBHist (countablyBasedUniformityEncodeBHist D))
            (countablyBasedUniformityDecodeBHist (countablyBasedUniformityEncodeBHist R))
            (countablyBasedUniformityDecodeBHist (countablyBasedUniformityEncodeBHist H))
            (countablyBasedUniformityDecodeBHist (countablyBasedUniformityEncodeBHist C))
            (countablyBasedUniformityDecodeBHist (countablyBasedUniformityEncodeBHist P))
            (countablyBasedUniformityDecodeBHist (countablyBasedUniformityEncodeBHist N))) =
          some (CountablyBasedUniformityUp.mk E F S Q D R H C P N)
      rw [CountablyBasedUniformityTasteGate_single_carrier_alignment_decode E,
        CountablyBasedUniformityTasteGate_single_carrier_alignment_decode F,
        CountablyBasedUniformityTasteGate_single_carrier_alignment_decode S,
        CountablyBasedUniformityTasteGate_single_carrier_alignment_decode Q,
        CountablyBasedUniformityTasteGate_single_carrier_alignment_decode D,
        CountablyBasedUniformityTasteGate_single_carrier_alignment_decode R,
        CountablyBasedUniformityTasteGate_single_carrier_alignment_decode H,
        CountablyBasedUniformityTasteGate_single_carrier_alignment_decode C,
        CountablyBasedUniformityTasteGate_single_carrier_alignment_decode P,
        CountablyBasedUniformityTasteGate_single_carrier_alignment_decode N]

private theorem CountablyBasedUniformityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CountablyBasedUniformityUp} :
    countablyBasedUniformityToEventFlow x = countablyBasedUniformityToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      countablyBasedUniformityFromEventFlow (countablyBasedUniformityToEventFlow x) =
        countablyBasedUniformityFromEventFlow (countablyBasedUniformityToEventFlow y) :=
    congrArg countablyBasedUniformityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CountablyBasedUniformityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CountablyBasedUniformityTasteGate_single_carrier_alignment_round_trip y)))

instance countablyBasedUniformityBHistCarrier :
    BHistCarrier CountablyBasedUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := countablyBasedUniformityToEventFlow
  fromEventFlow := countablyBasedUniformityFromEventFlow

instance countablyBasedUniformityChapterTasteGate :
    ChapterTasteGate CountablyBasedUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change countablyBasedUniformityFromEventFlow (countablyBasedUniformityToEventFlow x) = some x
    exact CountablyBasedUniformityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CountablyBasedUniformityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CountablyBasedUniformityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  countablyBasedUniformityChapterTasteGate

theorem CountablyBasedUniformityTasteGate_single_carrier_alignment :
    (forall h : BHist,
      countablyBasedUniformityDecodeBHist (countablyBasedUniformityEncodeBHist h) = h) /\
      (forall x : CountablyBasedUniformityUp,
        countablyBasedUniformityFromEventFlow (countablyBasedUniformityToEventFlow x) =
          some x) /\
        (forall x y : CountablyBasedUniformityUp,
          countablyBasedUniformityToEventFlow x = countablyBasedUniformityToEventFlow y ->
            x = y) /\
          countablyBasedUniformityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CountablyBasedUniformityTasteGate_single_carrier_alignment_decode,
      CountablyBasedUniformityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CountablyBasedUniformityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CountablyBasedUniformityUp
