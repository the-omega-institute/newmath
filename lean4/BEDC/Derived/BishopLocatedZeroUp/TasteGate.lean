import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedZeroUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedZeroUp : Type where
  | mk (B M S Q A H C P N : BHist) : BishopLocatedZeroUp
  deriving DecidableEq

def bishopLocatedZeroEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedZeroEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedZeroEncodeBHist h

def bishopLocatedZeroDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedZeroDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedZeroDecodeBHist tail)

private theorem BishopLocatedZeroTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bishopLocatedZeroDecodeBHist (bishopLocatedZeroEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedZeroFields : BishopLocatedZeroUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedZeroUp.mk B M S Q A H C P N => [B, M, S, Q, A, H, C, P, N]

def bishopLocatedZeroToEventFlow : BishopLocatedZeroUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopLocatedZeroFields x).map bishopLocatedZeroEncodeBHist

private def bishopLocatedZeroEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopLocatedZeroEventAtDefault index rest

def bishopLocatedZeroFromEventFlow (ef : EventFlow) : Option BishopLocatedZeroUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedZeroUp.mk
      (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEventAtDefault 0 ef))
      (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEventAtDefault 1 ef))
      (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEventAtDefault 2 ef))
      (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEventAtDefault 3 ef))
      (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEventAtDefault 4 ef))
      (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEventAtDefault 5 ef))
      (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEventAtDefault 6 ef))
      (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEventAtDefault 7 ef))
      (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEventAtDefault 8 ef)))

private theorem BishopLocatedZeroTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopLocatedZeroUp,
      bishopLocatedZeroFromEventFlow (bishopLocatedZeroToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B M S Q A H C P N =>
      change
        some
            (BishopLocatedZeroUp.mk
              (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEncodeBHist B))
              (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEncodeBHist M))
              (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEncodeBHist S))
              (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEncodeBHist Q))
              (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEncodeBHist A))
              (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEncodeBHist H))
              (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEncodeBHist C))
              (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEncodeBHist P))
              (bishopLocatedZeroDecodeBHist (bishopLocatedZeroEncodeBHist N))) =
          some (BishopLocatedZeroUp.mk B M S Q A H C P N)
      rw [BishopLocatedZeroTasteGate_single_carrier_alignment_decode_encode B,
        BishopLocatedZeroTasteGate_single_carrier_alignment_decode_encode M,
        BishopLocatedZeroTasteGate_single_carrier_alignment_decode_encode S,
        BishopLocatedZeroTasteGate_single_carrier_alignment_decode_encode Q,
        BishopLocatedZeroTasteGate_single_carrier_alignment_decode_encode A,
        BishopLocatedZeroTasteGate_single_carrier_alignment_decode_encode H,
        BishopLocatedZeroTasteGate_single_carrier_alignment_decode_encode C,
        BishopLocatedZeroTasteGate_single_carrier_alignment_decode_encode P,
        BishopLocatedZeroTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopLocatedZeroTasteGate_single_carrier_alignment_injective
    {x y : BishopLocatedZeroUp} :
    bishopLocatedZeroToEventFlow x = bishopLocatedZeroToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedZeroFromEventFlow (bishopLocatedZeroToEventFlow x) =
        bishopLocatedZeroFromEventFlow (bishopLocatedZeroToEventFlow y) :=
    congrArg bishopLocatedZeroFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopLocatedZeroTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BishopLocatedZeroTasteGate_single_carrier_alignment_round_trip y)))

private theorem bishopLocatedZeroFields_faithful :
    ∀ x y : BishopLocatedZeroUp, bishopLocatedZeroFields x = bishopLocatedZeroFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 M1 S1 Q1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 M2 S2 Q2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopLocatedZeroBHistCarrier : BHistCarrier BishopLocatedZeroUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedZeroToEventFlow
  fromEventFlow := bishopLocatedZeroFromEventFlow

instance bishopLocatedZeroChapterTasteGate : ChapterTasteGate BishopLocatedZeroUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopLocatedZeroFromEventFlow (bishopLocatedZeroToEventFlow x) = some x
    exact BishopLocatedZeroTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopLocatedZeroTasteGate_single_carrier_alignment_injective heq)

instance bishopLocatedZeroFieldFaithful : FieldFaithful BishopLocatedZeroUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopLocatedZeroFields
  field_faithful := bishopLocatedZeroFields_faithful

instance bishopLocatedZeroNontrivial : Nontrivial BishopLocatedZeroUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopLocatedZeroUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopLocatedZeroUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopLocatedZeroUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedZeroChapterTasteGate

theorem BishopLocatedZeroTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopLocatedZeroDecodeBHist (bishopLocatedZeroEncodeBHist h) = h) ∧
      (∀ x : BishopLocatedZeroUp,
        bishopLocatedZeroFromEventFlow (bishopLocatedZeroToEventFlow x) = some x) ∧
        (∀ x y : BishopLocatedZeroUp,
          bishopLocatedZeroToEventFlow x = bishopLocatedZeroToEventFlow y → x = y) ∧
          bishopLocatedZeroEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopLocatedZeroTasteGate_single_carrier_alignment_decode_encode,
      BishopLocatedZeroTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact BishopLocatedZeroTasteGate_single_carrier_alignment_injective heq,
      rfl⟩

end BEDC.Derived.BishopLocatedZeroUp
