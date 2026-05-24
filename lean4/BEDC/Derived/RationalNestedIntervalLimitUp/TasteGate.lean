import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalNestedIntervalLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalNestedIntervalLimitUp : Type where
  | mk (I W E R S H C P N : BHist) : RationalNestedIntervalLimitUp
  deriving DecidableEq

def rationalNestedIntervalLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalNestedIntervalLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalNestedIntervalLimitEncodeBHist h

def rationalNestedIntervalLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalNestedIntervalLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalNestedIntervalLimitDecodeBHist tail)

private theorem rationalNestedIntervalLimit_decode_encode :
    ∀ h : BHist,
      rationalNestedIntervalLimitDecodeBHist (rationalNestedIntervalLimitEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rationalNestedIntervalLimitFields : RationalNestedIntervalLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalNestedIntervalLimitUp.mk I W E R S H C P N => [I, W, E, R, S, H, C, P, N]

def rationalNestedIntervalLimitToEventFlow : RationalNestedIntervalLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RationalNestedIntervalLimitUp.mk I W E R S H C P N =>
      [rationalNestedIntervalLimitEncodeBHist I, rationalNestedIntervalLimitEncodeBHist W,
        rationalNestedIntervalLimitEncodeBHist E, rationalNestedIntervalLimitEncodeBHist R,
        rationalNestedIntervalLimitEncodeBHist S, rationalNestedIntervalLimitEncodeBHist H,
        rationalNestedIntervalLimitEncodeBHist C, rationalNestedIntervalLimitEncodeBHist P,
        rationalNestedIntervalLimitEncodeBHist N]

def rationalNestedIntervalLimitFromEventFlow :
    EventFlow → Option RationalNestedIntervalLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | E :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | S :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (RationalNestedIntervalLimitUp.mk
                                              (rationalNestedIntervalLimitDecodeBHist I)
                                              (rationalNestedIntervalLimitDecodeBHist W)
                                              (rationalNestedIntervalLimitDecodeBHist E)
                                              (rationalNestedIntervalLimitDecodeBHist R)
                                              (rationalNestedIntervalLimitDecodeBHist S)
                                              (rationalNestedIntervalLimitDecodeBHist H)
                                              (rationalNestedIntervalLimitDecodeBHist C)
                                              (rationalNestedIntervalLimitDecodeBHist P)
                                              (rationalNestedIntervalLimitDecodeBHist N))
                                      | head :: tail => none

private theorem rationalNestedIntervalLimit_round_trip :
    ∀ x : RationalNestedIntervalLimitUp,
      rationalNestedIntervalLimitFromEventFlow
          (rationalNestedIntervalLimitToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I W E R S H C P N =>
      rw [rationalNestedIntervalLimitToEventFlow,
        rationalNestedIntervalLimitFromEventFlow,
        rationalNestedIntervalLimit_decode_encode I,
        rationalNestedIntervalLimit_decode_encode W,
        rationalNestedIntervalLimit_decode_encode E,
        rationalNestedIntervalLimit_decode_encode R,
        rationalNestedIntervalLimit_decode_encode S,
        rationalNestedIntervalLimit_decode_encode H,
        rationalNestedIntervalLimit_decode_encode C,
        rationalNestedIntervalLimit_decode_encode P,
        rationalNestedIntervalLimit_decode_encode N]

private theorem rationalNestedIntervalLimitToEventFlow_injective
    {x y : RationalNestedIntervalLimitUp} :
    rationalNestedIntervalLimitToEventFlow x = rationalNestedIntervalLimitToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalNestedIntervalLimitFromEventFlow (rationalNestedIntervalLimitToEventFlow x) =
        rationalNestedIntervalLimitFromEventFlow (rationalNestedIntervalLimitToEventFlow y) :=
    congrArg rationalNestedIntervalLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rationalNestedIntervalLimit_round_trip x).symm
      (Eq.trans hread (rationalNestedIntervalLimit_round_trip y)))

instance rationalNestedIntervalLimitBHistCarrier :
    BHistCarrier RationalNestedIntervalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalNestedIntervalLimitToEventFlow
  fromEventFlow := rationalNestedIntervalLimitFromEventFlow

private def rationalNestedIntervalLimitChapterTasteGateConcrete :
    @ChapterTasteGate RationalNestedIntervalLimitUp rationalNestedIntervalLimitBHistCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      rationalNestedIntervalLimitFromEventFlow (rationalNestedIntervalLimitToEventFlow x) =
        some x
    exact rationalNestedIntervalLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rationalNestedIntervalLimitToEventFlow_injective heq)

instance rationalNestedIntervalLimitChapterTasteGate :
    ChapterTasteGate RationalNestedIntervalLimitUp :=
  rationalNestedIntervalLimitChapterTasteGateConcrete

def taste_gate : ChapterTasteGate RationalNestedIntervalLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rationalNestedIntervalLimitChapterTasteGateConcrete

theorem RationalNestedIntervalLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist, rationalNestedIntervalLimitDecodeBHist
        (rationalNestedIntervalLimitEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RationalNestedIntervalLimitUp) ∧
        Nonempty (ChapterTasteGate RationalNestedIntervalLimitUp) ∧
          rationalNestedIntervalLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rationalNestedIntervalLimit_decode_encode,
      ⟨rationalNestedIntervalLimitBHistCarrier⟩,
      ⟨rationalNestedIntervalLimitChapterTasteGateConcrete⟩,
      rfl⟩

end BEDC.Derived.RationalNestedIntervalLimitUp
