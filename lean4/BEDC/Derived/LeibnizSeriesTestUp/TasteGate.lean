import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LeibnizSeriesTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LeibnizSeriesTestUp : Type where
  | mk (S Sigma M T Q R E H C P N : BHist) : LeibnizSeriesTestUp
  deriving DecidableEq

def leibnizSeriesTestEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: leibnizSeriesTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: leibnizSeriesTestEncodeBHist h

def leibnizSeriesTestDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (leibnizSeriesTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (leibnizSeriesTestDecodeBHist tail)

private theorem LeibnizSeriesTestTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, leibnizSeriesTestDecodeBHist (leibnizSeriesTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def leibnizSeriesTestToEventFlow : LeibnizSeriesTestUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LeibnizSeriesTestUp.mk S Sigma M T Q R E H C P N =>
      [leibnizSeriesTestEncodeBHist S,
        leibnizSeriesTestEncodeBHist Sigma,
        leibnizSeriesTestEncodeBHist M,
        leibnizSeriesTestEncodeBHist T,
        leibnizSeriesTestEncodeBHist Q,
        leibnizSeriesTestEncodeBHist R,
        leibnizSeriesTestEncodeBHist E,
        leibnizSeriesTestEncodeBHist H,
        leibnizSeriesTestEncodeBHist C,
        leibnizSeriesTestEncodeBHist P,
        leibnizSeriesTestEncodeBHist N]

def leibnizSeriesTestFromEventFlow : EventFlow → Option LeibnizSeriesTestUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | Sigma :: rest1 =>
          match rest1 with
          | [] => none
          | M :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | Q :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (LeibnizSeriesTestUp.mk
                                                      (leibnizSeriesTestDecodeBHist S)
                                                      (leibnizSeriesTestDecodeBHist Sigma)
                                                      (leibnizSeriesTestDecodeBHist M)
                                                      (leibnizSeriesTestDecodeBHist T)
                                                      (leibnizSeriesTestDecodeBHist Q)
                                                      (leibnizSeriesTestDecodeBHist R)
                                                      (leibnizSeriesTestDecodeBHist E)
                                                      (leibnizSeriesTestDecodeBHist H)
                                                      (leibnizSeriesTestDecodeBHist C)
                                                      (leibnizSeriesTestDecodeBHist P)
                                                      (leibnizSeriesTestDecodeBHist N))
                                              | _ :: _ => none

private theorem LeibnizSeriesTestTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LeibnizSeriesTestUp,
      leibnizSeriesTestFromEventFlow (leibnizSeriesTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Sigma M T Q R E H C P N =>
      change
        some
          (LeibnizSeriesTestUp.mk
            (leibnizSeriesTestDecodeBHist (leibnizSeriesTestEncodeBHist S))
            (leibnizSeriesTestDecodeBHist (leibnizSeriesTestEncodeBHist Sigma))
            (leibnizSeriesTestDecodeBHist (leibnizSeriesTestEncodeBHist M))
            (leibnizSeriesTestDecodeBHist (leibnizSeriesTestEncodeBHist T))
            (leibnizSeriesTestDecodeBHist (leibnizSeriesTestEncodeBHist Q))
            (leibnizSeriesTestDecodeBHist (leibnizSeriesTestEncodeBHist R))
            (leibnizSeriesTestDecodeBHist (leibnizSeriesTestEncodeBHist E))
            (leibnizSeriesTestDecodeBHist (leibnizSeriesTestEncodeBHist H))
            (leibnizSeriesTestDecodeBHist (leibnizSeriesTestEncodeBHist C))
            (leibnizSeriesTestDecodeBHist (leibnizSeriesTestEncodeBHist P))
            (leibnizSeriesTestDecodeBHist (leibnizSeriesTestEncodeBHist N))) =
          some (LeibnizSeriesTestUp.mk S Sigma M T Q R E H C P N)
      rw [LeibnizSeriesTestTasteGate_single_carrier_alignment_decode S,
        LeibnizSeriesTestTasteGate_single_carrier_alignment_decode Sigma,
        LeibnizSeriesTestTasteGate_single_carrier_alignment_decode M,
        LeibnizSeriesTestTasteGate_single_carrier_alignment_decode T,
        LeibnizSeriesTestTasteGate_single_carrier_alignment_decode Q,
        LeibnizSeriesTestTasteGate_single_carrier_alignment_decode R,
        LeibnizSeriesTestTasteGate_single_carrier_alignment_decode E,
        LeibnizSeriesTestTasteGate_single_carrier_alignment_decode H,
        LeibnizSeriesTestTasteGate_single_carrier_alignment_decode C,
        LeibnizSeriesTestTasteGate_single_carrier_alignment_decode P,
        LeibnizSeriesTestTasteGate_single_carrier_alignment_decode N]

private theorem LeibnizSeriesTestTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LeibnizSeriesTestUp} :
    leibnizSeriesTestToEventFlow x = leibnizSeriesTestToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      leibnizSeriesTestFromEventFlow (leibnizSeriesTestToEventFlow x) =
        leibnizSeriesTestFromEventFlow (leibnizSeriesTestToEventFlow y) :=
    congrArg leibnizSeriesTestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LeibnizSeriesTestTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LeibnizSeriesTestTasteGate_single_carrier_alignment_round_trip y)))

instance leibnizSeriesTestBHistCarrier : BHistCarrier LeibnizSeriesTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := leibnizSeriesTestToEventFlow
  fromEventFlow := leibnizSeriesTestFromEventFlow

instance leibnizSeriesTestChapterTasteGate :
    ChapterTasteGate LeibnizSeriesTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change leibnizSeriesTestFromEventFlow (leibnizSeriesTestToEventFlow x) = some x
    exact LeibnizSeriesTestTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LeibnizSeriesTestTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LeibnizSeriesTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  leibnizSeriesTestChapterTasteGate

theorem LeibnizSeriesTestTasteGate_single_carrier_alignment :
    (∀ h : BHist, leibnizSeriesTestDecodeBHist (leibnizSeriesTestEncodeBHist h) = h) ∧
      (∀ x : LeibnizSeriesTestUp,
        leibnizSeriesTestFromEventFlow (leibnizSeriesTestToEventFlow x) = some x) ∧
        (∀ x y : LeibnizSeriesTestUp,
          leibnizSeriesTestToEventFlow x = leibnizSeriesTestToEventFlow y → x = y) ∧
          leibnizSeriesTestEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LeibnizSeriesTestTasteGate_single_carrier_alignment_decode,
      LeibnizSeriesTestTasteGate_single_carrier_alignment_round_trip,
      fun _x _y => LeibnizSeriesTestTasteGate_single_carrier_alignment_toEventFlow_injective,
      rfl⟩

end BEDC.Derived.LeibnizSeriesTestUp
