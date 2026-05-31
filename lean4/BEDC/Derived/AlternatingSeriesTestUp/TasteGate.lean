import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AlternatingSeriesTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AlternatingSeriesTestUp : Type where
  | mk (S Sigma M T R E H C P N : BHist) : AlternatingSeriesTestUp
  deriving DecidableEq

def alternatingSeriesTestEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: alternatingSeriesTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: alternatingSeriesTestEncodeBHist h

def alternatingSeriesTestDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (alternatingSeriesTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (alternatingSeriesTestDecodeBHist tail)

private theorem AlternatingSeriesTestTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      alternatingSeriesTestDecodeBHist (alternatingSeriesTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def alternatingSeriesTestToEventFlow : AlternatingSeriesTestUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AlternatingSeriesTestUp.mk S Sigma M T R E H C P N =>
      [alternatingSeriesTestEncodeBHist S,
        alternatingSeriesTestEncodeBHist Sigma,
        alternatingSeriesTestEncodeBHist M,
        alternatingSeriesTestEncodeBHist T,
        alternatingSeriesTestEncodeBHist R,
        alternatingSeriesTestEncodeBHist E,
        alternatingSeriesTestEncodeBHist H,
        alternatingSeriesTestEncodeBHist C,
        alternatingSeriesTestEncodeBHist P,
        alternatingSeriesTestEncodeBHist N]

def alternatingSeriesTestFromEventFlow : EventFlow -> Option AlternatingSeriesTestUp
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
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
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
                                                (AlternatingSeriesTestUp.mk
                                                  (alternatingSeriesTestDecodeBHist S)
                                                  (alternatingSeriesTestDecodeBHist Sigma)
                                                  (alternatingSeriesTestDecodeBHist M)
                                                  (alternatingSeriesTestDecodeBHist T)
                                                  (alternatingSeriesTestDecodeBHist R)
                                                  (alternatingSeriesTestDecodeBHist E)
                                                  (alternatingSeriesTestDecodeBHist H)
                                                  (alternatingSeriesTestDecodeBHist C)
                                                  (alternatingSeriesTestDecodeBHist P)
                                                  (alternatingSeriesTestDecodeBHist N))
                                          | _ :: _ => none

private theorem AlternatingSeriesTestTasteGate_single_carrier_alignment_round_trip :
    forall x : AlternatingSeriesTestUp,
      alternatingSeriesTestFromEventFlow (alternatingSeriesTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Sigma M T R E H C P N =>
      change
        some
          (AlternatingSeriesTestUp.mk
            (alternatingSeriesTestDecodeBHist (alternatingSeriesTestEncodeBHist S))
            (alternatingSeriesTestDecodeBHist (alternatingSeriesTestEncodeBHist Sigma))
            (alternatingSeriesTestDecodeBHist (alternatingSeriesTestEncodeBHist M))
            (alternatingSeriesTestDecodeBHist (alternatingSeriesTestEncodeBHist T))
            (alternatingSeriesTestDecodeBHist (alternatingSeriesTestEncodeBHist R))
            (alternatingSeriesTestDecodeBHist (alternatingSeriesTestEncodeBHist E))
            (alternatingSeriesTestDecodeBHist (alternatingSeriesTestEncodeBHist H))
            (alternatingSeriesTestDecodeBHist (alternatingSeriesTestEncodeBHist C))
            (alternatingSeriesTestDecodeBHist (alternatingSeriesTestEncodeBHist P))
            (alternatingSeriesTestDecodeBHist (alternatingSeriesTestEncodeBHist N))) =
          some (AlternatingSeriesTestUp.mk S Sigma M T R E H C P N)
      rw [AlternatingSeriesTestTasteGate_single_carrier_alignment_decode S,
        AlternatingSeriesTestTasteGate_single_carrier_alignment_decode Sigma,
        AlternatingSeriesTestTasteGate_single_carrier_alignment_decode M,
        AlternatingSeriesTestTasteGate_single_carrier_alignment_decode T,
        AlternatingSeriesTestTasteGate_single_carrier_alignment_decode R,
        AlternatingSeriesTestTasteGate_single_carrier_alignment_decode E,
        AlternatingSeriesTestTasteGate_single_carrier_alignment_decode H,
        AlternatingSeriesTestTasteGate_single_carrier_alignment_decode C,
        AlternatingSeriesTestTasteGate_single_carrier_alignment_decode P,
        AlternatingSeriesTestTasteGate_single_carrier_alignment_decode N]

private theorem AlternatingSeriesTestTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AlternatingSeriesTestUp} :
    alternatingSeriesTestToEventFlow x = alternatingSeriesTestToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      alternatingSeriesTestFromEventFlow (alternatingSeriesTestToEventFlow x) =
        alternatingSeriesTestFromEventFlow (alternatingSeriesTestToEventFlow y) :=
    congrArg alternatingSeriesTestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (AlternatingSeriesTestTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (AlternatingSeriesTestTasteGate_single_carrier_alignment_round_trip y)))

instance alternatingSeriesTestBHistCarrier : BHistCarrier AlternatingSeriesTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := alternatingSeriesTestToEventFlow
  fromEventFlow := alternatingSeriesTestFromEventFlow

instance alternatingSeriesTestChapterTasteGate : ChapterTasteGate AlternatingSeriesTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change alternatingSeriesTestFromEventFlow (alternatingSeriesTestToEventFlow x) = some x
    exact AlternatingSeriesTestTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AlternatingSeriesTestTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate AlternatingSeriesTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  alternatingSeriesTestChapterTasteGate

theorem AlternatingSeriesTestTasteGate_single_carrier_alignment :
    (∀ h : BHist, alternatingSeriesTestDecodeBHist (alternatingSeriesTestEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier AlternatingSeriesTestUp) ∧
        Nonempty (ChapterTasteGate AlternatingSeriesTestUp) ∧
          alternatingSeriesTestEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨AlternatingSeriesTestTasteGate_single_carrier_alignment_decode,
      ⟨alternatingSeriesTestBHistCarrier⟩,
      ⟨alternatingSeriesTestChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.AlternatingSeriesTestUp
