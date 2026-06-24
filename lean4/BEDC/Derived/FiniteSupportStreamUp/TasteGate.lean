import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteSupportStreamUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteSupportStreamUp : Type where
  | mk (S B L D R Q H C P N : BHist) : FiniteSupportStreamUp
  deriving DecidableEq

def finiteSupportStreamEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteSupportStreamEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteSupportStreamEncodeBHist h

def finiteSupportStreamDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteSupportStreamDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteSupportStreamDecodeBHist tail)

private theorem FiniteSupportStreamTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, finiteSupportStreamDecodeBHist (finiteSupportStreamEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteSupportStreamFields : FiniteSupportStreamUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteSupportStreamUp.mk S B L D R Q H C P N => [S, B, L, D, R, Q, H, C, P, N]

def finiteSupportStreamToEventFlow : FiniteSupportStreamUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteSupportStreamFields x).map finiteSupportStreamEncodeBHist

private def finiteSupportStreamEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteSupportStreamEventAtDefault index rest

def finiteSupportStreamFromEventFlow (ef : EventFlow) : Option FiniteSupportStreamUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteSupportStreamUp.mk
      (finiteSupportStreamDecodeBHist (finiteSupportStreamEventAtDefault 0 ef))
      (finiteSupportStreamDecodeBHist (finiteSupportStreamEventAtDefault 1 ef))
      (finiteSupportStreamDecodeBHist (finiteSupportStreamEventAtDefault 2 ef))
      (finiteSupportStreamDecodeBHist (finiteSupportStreamEventAtDefault 3 ef))
      (finiteSupportStreamDecodeBHist (finiteSupportStreamEventAtDefault 4 ef))
      (finiteSupportStreamDecodeBHist (finiteSupportStreamEventAtDefault 5 ef))
      (finiteSupportStreamDecodeBHist (finiteSupportStreamEventAtDefault 6 ef))
      (finiteSupportStreamDecodeBHist (finiteSupportStreamEventAtDefault 7 ef))
      (finiteSupportStreamDecodeBHist (finiteSupportStreamEventAtDefault 8 ef))
      (finiteSupportStreamDecodeBHist (finiteSupportStreamEventAtDefault 9 ef)))

private theorem FiniteSupportStreamTasteGate_single_carrier_alignment_round_trip
    (x : FiniteSupportStreamUp) :
    finiteSupportStreamFromEventFlow (finiteSupportStreamToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S B L D R Q H C P N =>
      change
        some
          (FiniteSupportStreamUp.mk
            (finiteSupportStreamDecodeBHist (finiteSupportStreamEncodeBHist S))
            (finiteSupportStreamDecodeBHist (finiteSupportStreamEncodeBHist B))
            (finiteSupportStreamDecodeBHist (finiteSupportStreamEncodeBHist L))
            (finiteSupportStreamDecodeBHist (finiteSupportStreamEncodeBHist D))
            (finiteSupportStreamDecodeBHist (finiteSupportStreamEncodeBHist R))
            (finiteSupportStreamDecodeBHist (finiteSupportStreamEncodeBHist Q))
            (finiteSupportStreamDecodeBHist (finiteSupportStreamEncodeBHist H))
            (finiteSupportStreamDecodeBHist (finiteSupportStreamEncodeBHist C))
            (finiteSupportStreamDecodeBHist (finiteSupportStreamEncodeBHist P))
            (finiteSupportStreamDecodeBHist (finiteSupportStreamEncodeBHist N))) =
          some (FiniteSupportStreamUp.mk S B L D R Q H C P N)
      rw [FiniteSupportStreamTasteGate_single_carrier_alignment_decode_encode S,
        FiniteSupportStreamTasteGate_single_carrier_alignment_decode_encode B,
        FiniteSupportStreamTasteGate_single_carrier_alignment_decode_encode L,
        FiniteSupportStreamTasteGate_single_carrier_alignment_decode_encode D,
        FiniteSupportStreamTasteGate_single_carrier_alignment_decode_encode R,
        FiniteSupportStreamTasteGate_single_carrier_alignment_decode_encode Q,
        FiniteSupportStreamTasteGate_single_carrier_alignment_decode_encode H,
        FiniteSupportStreamTasteGate_single_carrier_alignment_decode_encode C,
        FiniteSupportStreamTasteGate_single_carrier_alignment_decode_encode P,
        FiniteSupportStreamTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiniteSupportStreamTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteSupportStreamUp} :
    finiteSupportStreamToEventFlow x = finiteSupportStreamToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteSupportStreamFromEventFlow (finiteSupportStreamToEventFlow x) =
        finiteSupportStreamFromEventFlow (finiteSupportStreamToEventFlow y) :=
    congrArg finiteSupportStreamFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteSupportStreamTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteSupportStreamTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteSupportStreamTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : FiniteSupportStreamUp, finiteSupportStreamFields x = finiteSupportStreamFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 B1 L1 D1 R1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 B2 L2 D2 R2 Q2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteSupportStreamBHistCarrier : BHistCarrier FiniteSupportStreamUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteSupportStreamToEventFlow
  fromEventFlow := finiteSupportStreamFromEventFlow

instance finiteSupportStreamChapterTasteGate : ChapterTasteGate FiniteSupportStreamUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteSupportStreamFromEventFlow (finiteSupportStreamToEventFlow x) = some x
    exact FiniteSupportStreamTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteSupportStreamTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate FiniteSupportStreamUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteSupportStreamChapterTasteGate

theorem FiniteSupportStreamTasteGate_single_carrier_alignment :
    ChapterTasteGate FiniteSupportStreamUp ∧ finiteSupportStreamEncodeBHist BHist.Empty = [] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨finiteSupportStreamChapterTasteGate, rfl⟩

end BEDC.Derived.FiniteSupportStreamUp
