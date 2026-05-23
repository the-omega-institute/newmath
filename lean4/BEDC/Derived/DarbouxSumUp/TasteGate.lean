import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DarbouxSumUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DarbouxSumUp : Type where
  | mk (I P L U S R B E H N : BHist) : DarbouxSumUp
  deriving DecidableEq

def darbouxSumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: darbouxSumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: darbouxSumEncodeBHist h

def darbouxSumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (darbouxSumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (darbouxSumDecodeBHist tail)

private theorem DarbouxSumTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, darbouxSumDecodeBHist (darbouxSumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def darbouxSumFields : DarbouxSumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DarbouxSumUp.mk I P L U S R B E H N => [I, P, L, U, S, R, B, E, H, N]

def darbouxSumToEventFlow : DarbouxSumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (darbouxSumFields x).map darbouxSumEncodeBHist

private def DarbouxSumTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      DarbouxSumTasteGate_single_carrier_alignment_eventAt index rest

def darbouxSumFromEventFlow (ef : EventFlow) : Option DarbouxSumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DarbouxSumUp.mk
      (darbouxSumDecodeBHist (DarbouxSumTasteGate_single_carrier_alignment_eventAt 0 ef))
      (darbouxSumDecodeBHist (DarbouxSumTasteGate_single_carrier_alignment_eventAt 1 ef))
      (darbouxSumDecodeBHist (DarbouxSumTasteGate_single_carrier_alignment_eventAt 2 ef))
      (darbouxSumDecodeBHist (DarbouxSumTasteGate_single_carrier_alignment_eventAt 3 ef))
      (darbouxSumDecodeBHist (DarbouxSumTasteGate_single_carrier_alignment_eventAt 4 ef))
      (darbouxSumDecodeBHist (DarbouxSumTasteGate_single_carrier_alignment_eventAt 5 ef))
      (darbouxSumDecodeBHist (DarbouxSumTasteGate_single_carrier_alignment_eventAt 6 ef))
      (darbouxSumDecodeBHist (DarbouxSumTasteGate_single_carrier_alignment_eventAt 7 ef))
      (darbouxSumDecodeBHist (DarbouxSumTasteGate_single_carrier_alignment_eventAt 8 ef))
      (darbouxSumDecodeBHist (DarbouxSumTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem DarbouxSumTasteGate_single_carrier_alignment_round_trip
    (x : DarbouxSumUp) :
    darbouxSumFromEventFlow (darbouxSumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I P L U S R B E H N =>
      change
        some
          (DarbouxSumUp.mk
            (darbouxSumDecodeBHist (darbouxSumEncodeBHist I))
            (darbouxSumDecodeBHist (darbouxSumEncodeBHist P))
            (darbouxSumDecodeBHist (darbouxSumEncodeBHist L))
            (darbouxSumDecodeBHist (darbouxSumEncodeBHist U))
            (darbouxSumDecodeBHist (darbouxSumEncodeBHist S))
            (darbouxSumDecodeBHist (darbouxSumEncodeBHist R))
            (darbouxSumDecodeBHist (darbouxSumEncodeBHist B))
            (darbouxSumDecodeBHist (darbouxSumEncodeBHist E))
            (darbouxSumDecodeBHist (darbouxSumEncodeBHist H))
            (darbouxSumDecodeBHist (darbouxSumEncodeBHist N))) =
          some (DarbouxSumUp.mk I P L U S R B E H N)
      rw [DarbouxSumTasteGate_single_carrier_alignment_decode_encode I,
        DarbouxSumTasteGate_single_carrier_alignment_decode_encode P,
        DarbouxSumTasteGate_single_carrier_alignment_decode_encode L,
        DarbouxSumTasteGate_single_carrier_alignment_decode_encode U,
        DarbouxSumTasteGate_single_carrier_alignment_decode_encode S,
        DarbouxSumTasteGate_single_carrier_alignment_decode_encode R,
        DarbouxSumTasteGate_single_carrier_alignment_decode_encode B,
        DarbouxSumTasteGate_single_carrier_alignment_decode_encode E,
        DarbouxSumTasteGate_single_carrier_alignment_decode_encode H,
        DarbouxSumTasteGate_single_carrier_alignment_decode_encode N]

private theorem DarbouxSumTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DarbouxSumUp} :
    darbouxSumToEventFlow x = darbouxSumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      darbouxSumFromEventFlow (darbouxSumToEventFlow x) =
        darbouxSumFromEventFlow (darbouxSumToEventFlow y) :=
    congrArg darbouxSumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DarbouxSumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DarbouxSumTasteGate_single_carrier_alignment_round_trip y)))

private theorem DarbouxSumTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : DarbouxSumUp, darbouxSumFields x = darbouxSumFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ P₁ L₁ U₁ S₁ R₁ B₁ E₁ H₁ N₁ =>
      cases y with
      | mk I₂ P₂ L₂ U₂ S₂ R₂ B₂ E₂ H₂ N₂ =>
          cases hfields
          rfl

instance darbouxSumBHistCarrier : BHistCarrier DarbouxSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := darbouxSumToEventFlow
  fromEventFlow := darbouxSumFromEventFlow

instance darbouxSumChapterTasteGate : ChapterTasteGate DarbouxSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change darbouxSumFromEventFlow (darbouxSumToEventFlow x) = some x
    exact DarbouxSumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DarbouxSumTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance darbouxSumFieldFaithful : FieldFaithful DarbouxSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := darbouxSumFields
  field_faithful := DarbouxSumTasteGate_single_carrier_alignment_fields_faithful

instance darbouxSumNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DarbouxSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DarbouxSumUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DarbouxSumUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def darbouxSumTasteGate : ChapterTasteGate DarbouxSumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  darbouxSumChapterTasteGate

theorem DarbouxSumTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DarbouxSumUp) ∧
      Nonempty (FieldFaithful DarbouxSumUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DarbouxSumUp) ∧
          (∀ h : BHist, darbouxSumDecodeBHist (darbouxSumEncodeBHist h) = h) ∧
            (∀ x : DarbouxSumUp,
              darbouxSumFromEventFlow (darbouxSumToEventFlow x) = some x) ∧
              (∀ x y : DarbouxSumUp,
                darbouxSumToEventFlow x = darbouxSumToEventFlow y → x = y) ∧
                darbouxSumEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨darbouxSumChapterTasteGate⟩,
      ⟨darbouxSumFieldFaithful⟩,
      ⟨darbouxSumNontrivial⟩,
      DarbouxSumTasteGate_single_carrier_alignment_decode_encode,
      DarbouxSumTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => DarbouxSumTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DarbouxSumUp.TasteGate
