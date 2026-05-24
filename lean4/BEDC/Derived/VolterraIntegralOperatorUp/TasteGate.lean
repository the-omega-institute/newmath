import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.VolterraIntegralOperatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive VolterraIntegralOperatorUp : Type where
  | mk (I T X Y G M Q S R L E H C P N : BHist) : VolterraIntegralOperatorUp
  deriving DecidableEq

def volterraIntegralOperatorEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: volterraIntegralOperatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: volterraIntegralOperatorEncodeBHist h

def volterraIntegralOperatorDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (volterraIntegralOperatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (volterraIntegralOperatorDecodeBHist tail)

private theorem VolterraIntegralOperatorTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def volterraIntegralOperatorToEventFlow : VolterraIntegralOperatorUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | VolterraIntegralOperatorUp.mk I T X Y G M Q S R L E H C P N =>
      [volterraIntegralOperatorEncodeBHist I,
        volterraIntegralOperatorEncodeBHist T,
        volterraIntegralOperatorEncodeBHist X,
        volterraIntegralOperatorEncodeBHist Y,
        volterraIntegralOperatorEncodeBHist G,
        volterraIntegralOperatorEncodeBHist M,
        volterraIntegralOperatorEncodeBHist Q,
        volterraIntegralOperatorEncodeBHist S,
        volterraIntegralOperatorEncodeBHist R,
        volterraIntegralOperatorEncodeBHist L,
        volterraIntegralOperatorEncodeBHist E,
        volterraIntegralOperatorEncodeBHist H,
        volterraIntegralOperatorEncodeBHist C,
        volterraIntegralOperatorEncodeBHist P,
        volterraIntegralOperatorEncodeBHist N]

private def volterraIntegralOperatorEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => volterraIntegralOperatorEventAtDefault index rest

def volterraIntegralOperatorFromEventFlow
    (ef : EventFlow) : Option VolterraIntegralOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (VolterraIntegralOperatorUp.mk
      (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEventAtDefault 0 ef))
      (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEventAtDefault 1 ef))
      (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEventAtDefault 2 ef))
      (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEventAtDefault 3 ef))
      (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEventAtDefault 4 ef))
      (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEventAtDefault 5 ef))
      (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEventAtDefault 6 ef))
      (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEventAtDefault 7 ef))
      (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEventAtDefault 8 ef))
      (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEventAtDefault 9 ef))
      (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEventAtDefault 10 ef))
      (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEventAtDefault 11 ef))
      (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEventAtDefault 12 ef))
      (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEventAtDefault 13 ef))
      (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEventAtDefault 14 ef)))

private theorem VolterraIntegralOperatorTasteGate_single_carrier_alignment_round_trip :
    forall x : VolterraIntegralOperatorUp,
      volterraIntegralOperatorFromEventFlow (volterraIntegralOperatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I T X Y G M Q S R L E H C P N =>
      change
        some
          (VolterraIntegralOperatorUp.mk
            (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEncodeBHist I))
            (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEncodeBHist T))
            (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEncodeBHist X))
            (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEncodeBHist Y))
            (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEncodeBHist G))
            (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEncodeBHist M))
            (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEncodeBHist Q))
            (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEncodeBHist S))
            (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEncodeBHist R))
            (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEncodeBHist L))
            (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEncodeBHist E))
            (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEncodeBHist H))
            (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEncodeBHist C))
            (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEncodeBHist P))
            (volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEncodeBHist N))) =
          some (VolterraIntegralOperatorUp.mk I T X Y G M Q S R L E H C P N)
      rw [VolterraIntegralOperatorTasteGate_single_carrier_alignment_decode I,
        VolterraIntegralOperatorTasteGate_single_carrier_alignment_decode T,
        VolterraIntegralOperatorTasteGate_single_carrier_alignment_decode X,
        VolterraIntegralOperatorTasteGate_single_carrier_alignment_decode Y,
        VolterraIntegralOperatorTasteGate_single_carrier_alignment_decode G,
        VolterraIntegralOperatorTasteGate_single_carrier_alignment_decode M,
        VolterraIntegralOperatorTasteGate_single_carrier_alignment_decode Q,
        VolterraIntegralOperatorTasteGate_single_carrier_alignment_decode S,
        VolterraIntegralOperatorTasteGate_single_carrier_alignment_decode R,
        VolterraIntegralOperatorTasteGate_single_carrier_alignment_decode L,
        VolterraIntegralOperatorTasteGate_single_carrier_alignment_decode E,
        VolterraIntegralOperatorTasteGate_single_carrier_alignment_decode H,
        VolterraIntegralOperatorTasteGate_single_carrier_alignment_decode C,
        VolterraIntegralOperatorTasteGate_single_carrier_alignment_decode P,
        VolterraIntegralOperatorTasteGate_single_carrier_alignment_decode N]

private theorem VolterraIntegralOperatorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : VolterraIntegralOperatorUp} :
    volterraIntegralOperatorToEventFlow x = volterraIntegralOperatorToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      volterraIntegralOperatorFromEventFlow (volterraIntegralOperatorToEventFlow x) =
        volterraIntegralOperatorFromEventFlow (volterraIntegralOperatorToEventFlow y) :=
    congrArg volterraIntegralOperatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (VolterraIntegralOperatorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (VolterraIntegralOperatorTasteGate_single_carrier_alignment_round_trip y)))

private def volterraIntegralOperatorFields : VolterraIntegralOperatorUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | VolterraIntegralOperatorUp.mk I T X Y G M Q S R L E H C P N =>
      [I, T, X, Y, G, M, Q, S, R, L, E, H, C, P, N]

private theorem VolterraIntegralOperatorTasteGate_single_carrier_alignment_fields :
    forall x y : VolterraIntegralOperatorUp,
      volterraIntegralOperatorFields x = volterraIntegralOperatorFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 T1 X1 Y1 G1 M1 Q1 S1 R1 L1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 T2 X2 Y2 G2 M2 Q2 S2 R2 L2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance volterraIntegralOperatorBHistCarrier : BHistCarrier VolterraIntegralOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := volterraIntegralOperatorToEventFlow
  fromEventFlow := volterraIntegralOperatorFromEventFlow

instance volterraIntegralOperatorChapterTasteGate :
    ChapterTasteGate VolterraIntegralOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      volterraIntegralOperatorFromEventFlow (volterraIntegralOperatorToEventFlow x) = some x
    exact VolterraIntegralOperatorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (VolterraIntegralOperatorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance volterraIntegralOperatorFieldFaithful :
    FieldFaithful VolterraIntegralOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := volterraIntegralOperatorFields
  field_faithful := VolterraIntegralOperatorTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate VolterraIntegralOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  volterraIntegralOperatorChapterTasteGate

theorem VolterraIntegralOperatorTasteGate_single_carrier_alignment :
    (forall h : BHist,
      volterraIntegralOperatorDecodeBHist (volterraIntegralOperatorEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier VolterraIntegralOperatorUp) ∧
        Nonempty (ChapterTasteGate VolterraIntegralOperatorUp) ∧
          Nonempty (FieldFaithful VolterraIntegralOperatorUp) ∧
            volterraIntegralOperatorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨VolterraIntegralOperatorTasteGate_single_carrier_alignment_decode,
      ⟨volterraIntegralOperatorBHistCarrier⟩,
      ⟨volterraIntegralOperatorChapterTasteGate⟩,
      ⟨volterraIntegralOperatorFieldFaithful⟩,
      rfl⟩

end BEDC.Derived.VolterraIntegralOperatorUp
