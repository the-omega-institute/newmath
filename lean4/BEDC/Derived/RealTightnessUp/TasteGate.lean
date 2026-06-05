import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealTightnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealTightnessUp : Type where
  | mk (R D S Q I B O T H C P N : BHist) : RealTightnessUp
  deriving DecidableEq

def realTightnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realTightnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realTightnessEncodeBHist h

def realTightnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realTightnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realTightnessDecodeBHist tail)

private theorem RealTightnessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realTightnessDecodeBHist (realTightnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realTightnessFields : RealTightnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealTightnessUp.mk R D S Q I B O T H C P N => [R, D, S, Q, I, B, O, T, H, C, P, N]

def realTightnessToEventFlow : RealTightnessUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realTightnessFields x).map realTightnessEncodeBHist

private def realTightnessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realTightnessEventAtDefault index rest

def realTightnessFromEventFlow (ef : EventFlow) : Option RealTightnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealTightnessUp.mk
      (realTightnessDecodeBHist (realTightnessEventAtDefault 0 ef))
      (realTightnessDecodeBHist (realTightnessEventAtDefault 1 ef))
      (realTightnessDecodeBHist (realTightnessEventAtDefault 2 ef))
      (realTightnessDecodeBHist (realTightnessEventAtDefault 3 ef))
      (realTightnessDecodeBHist (realTightnessEventAtDefault 4 ef))
      (realTightnessDecodeBHist (realTightnessEventAtDefault 5 ef))
      (realTightnessDecodeBHist (realTightnessEventAtDefault 6 ef))
      (realTightnessDecodeBHist (realTightnessEventAtDefault 7 ef))
      (realTightnessDecodeBHist (realTightnessEventAtDefault 8 ef))
      (realTightnessDecodeBHist (realTightnessEventAtDefault 9 ef))
      (realTightnessDecodeBHist (realTightnessEventAtDefault 10 ef))
      (realTightnessDecodeBHist (realTightnessEventAtDefault 11 ef)))

private theorem RealTightnessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealTightnessUp,
      realTightnessFromEventFlow (realTightnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk R D S Q I B O T H C P N =>
      change
        some
          (RealTightnessUp.mk
            (realTightnessDecodeBHist (realTightnessEncodeBHist R))
            (realTightnessDecodeBHist (realTightnessEncodeBHist D))
            (realTightnessDecodeBHist (realTightnessEncodeBHist S))
            (realTightnessDecodeBHist (realTightnessEncodeBHist Q))
            (realTightnessDecodeBHist (realTightnessEncodeBHist I))
            (realTightnessDecodeBHist (realTightnessEncodeBHist B))
            (realTightnessDecodeBHist (realTightnessEncodeBHist O))
            (realTightnessDecodeBHist (realTightnessEncodeBHist T))
            (realTightnessDecodeBHist (realTightnessEncodeBHist H))
            (realTightnessDecodeBHist (realTightnessEncodeBHist C))
            (realTightnessDecodeBHist (realTightnessEncodeBHist P))
            (realTightnessDecodeBHist (realTightnessEncodeBHist N))) =
          some (RealTightnessUp.mk R D S Q I B O T H C P N)
      rw [RealTightnessTasteGate_single_carrier_alignment_decode R,
        RealTightnessTasteGate_single_carrier_alignment_decode D,
        RealTightnessTasteGate_single_carrier_alignment_decode S,
        RealTightnessTasteGate_single_carrier_alignment_decode Q,
        RealTightnessTasteGate_single_carrier_alignment_decode I,
        RealTightnessTasteGate_single_carrier_alignment_decode B,
        RealTightnessTasteGate_single_carrier_alignment_decode O,
        RealTightnessTasteGate_single_carrier_alignment_decode T,
        RealTightnessTasteGate_single_carrier_alignment_decode H,
        RealTightnessTasteGate_single_carrier_alignment_decode C,
        RealTightnessTasteGate_single_carrier_alignment_decode P,
        RealTightnessTasteGate_single_carrier_alignment_decode N]

private theorem RealTightnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealTightnessUp} :
    realTightnessToEventFlow x = realTightnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realTightnessFromEventFlow (realTightnessToEventFlow x) =
        realTightnessFromEventFlow (realTightnessToEventFlow y) :=
    congrArg realTightnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealTightnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealTightnessTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealTightnessTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealTightnessUp, realTightnessFields x = realTightnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 D1 S1 Q1 I1 B1 O1 T1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 D2 S2 Q2 I2 B2 O2 T2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realTightnessBHistCarrier : BHistCarrier RealTightnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realTightnessToEventFlow
  fromEventFlow := realTightnessFromEventFlow

instance realTightnessChapterTasteGate : ChapterTasteGate RealTightnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realTightnessFromEventFlow (realTightnessToEventFlow x) = some x
    exact RealTightnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealTightnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realTightnessFieldFaithful : FieldFaithful RealTightnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realTightnessFields
  field_faithful := RealTightnessTasteGate_single_carrier_alignment_fields

instance realTightnessNontrivial : Nontrivial RealTightnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealTightnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealTightnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealTightnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realTightnessChapterTasteGate

theorem RealTightnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, realTightnessDecodeBHist (realTightnessEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RealTightnessUp) ∧
        Nonempty (ChapterTasteGate RealTightnessUp) ∧
          realTightnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨RealTightnessTasteGate_single_carrier_alignment_decode,
      ⟨realTightnessBHistCarrier⟩, ⟨realTightnessChapterTasteGate⟩, rfl⟩

end BEDC.Derived.RealTightnessUp
