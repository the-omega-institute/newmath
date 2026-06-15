import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NashEquilibriumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NashEquilibriumUp : Type where
  | mk (P S A U B E H C Q N : BHist) : NashEquilibriumUp
  deriving DecidableEq

def nashEquilibriumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nashEquilibriumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nashEquilibriumEncodeBHist h

def nashEquilibriumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nashEquilibriumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nashEquilibriumDecodeBHist tail)

private theorem NashEquilibriumTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, nashEquilibriumDecodeBHist (nashEquilibriumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nashEquilibriumFields : NashEquilibriumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NashEquilibriumUp.mk P S A U B E H C Q N => [P, S, A, U, B, E, H, C, Q, N]

def nashEquilibriumToEventFlow : NashEquilibriumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (nashEquilibriumFields x).map nashEquilibriumEncodeBHist

private def nashEquilibriumEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => nashEquilibriumEventAt index rest

def nashEquilibriumFromEventFlow (ef : EventFlow) :
    Option NashEquilibriumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NashEquilibriumUp.mk
      (nashEquilibriumDecodeBHist (nashEquilibriumEventAt 0 ef))
      (nashEquilibriumDecodeBHist (nashEquilibriumEventAt 1 ef))
      (nashEquilibriumDecodeBHist (nashEquilibriumEventAt 2 ef))
      (nashEquilibriumDecodeBHist (nashEquilibriumEventAt 3 ef))
      (nashEquilibriumDecodeBHist (nashEquilibriumEventAt 4 ef))
      (nashEquilibriumDecodeBHist (nashEquilibriumEventAt 5 ef))
      (nashEquilibriumDecodeBHist (nashEquilibriumEventAt 6 ef))
      (nashEquilibriumDecodeBHist (nashEquilibriumEventAt 7 ef))
      (nashEquilibriumDecodeBHist (nashEquilibriumEventAt 8 ef))
      (nashEquilibriumDecodeBHist (nashEquilibriumEventAt 9 ef)))

private theorem NashEquilibriumTasteGate_single_carrier_alignment_round_trip
    (x : NashEquilibriumUp) :
    nashEquilibriumFromEventFlow (nashEquilibriumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk P S A U B E H C Q N =>
      change
        some
          (NashEquilibriumUp.mk
            (nashEquilibriumDecodeBHist (nashEquilibriumEncodeBHist P))
            (nashEquilibriumDecodeBHist (nashEquilibriumEncodeBHist S))
            (nashEquilibriumDecodeBHist (nashEquilibriumEncodeBHist A))
            (nashEquilibriumDecodeBHist (nashEquilibriumEncodeBHist U))
            (nashEquilibriumDecodeBHist (nashEquilibriumEncodeBHist B))
            (nashEquilibriumDecodeBHist (nashEquilibriumEncodeBHist E))
            (nashEquilibriumDecodeBHist (nashEquilibriumEncodeBHist H))
            (nashEquilibriumDecodeBHist (nashEquilibriumEncodeBHist C))
            (nashEquilibriumDecodeBHist (nashEquilibriumEncodeBHist Q))
            (nashEquilibriumDecodeBHist (nashEquilibriumEncodeBHist N))) =
          some (NashEquilibriumUp.mk P S A U B E H C Q N)
      rw [NashEquilibriumTasteGate_single_carrier_alignment_decode_encode P,
        NashEquilibriumTasteGate_single_carrier_alignment_decode_encode S,
        NashEquilibriumTasteGate_single_carrier_alignment_decode_encode A,
        NashEquilibriumTasteGate_single_carrier_alignment_decode_encode U,
        NashEquilibriumTasteGate_single_carrier_alignment_decode_encode B,
        NashEquilibriumTasteGate_single_carrier_alignment_decode_encode E,
        NashEquilibriumTasteGate_single_carrier_alignment_decode_encode H,
        NashEquilibriumTasteGate_single_carrier_alignment_decode_encode C,
        NashEquilibriumTasteGate_single_carrier_alignment_decode_encode Q,
        NashEquilibriumTasteGate_single_carrier_alignment_decode_encode N]

private theorem NashEquilibriumTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NashEquilibriumUp} :
    nashEquilibriumToEventFlow x = nashEquilibriumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nashEquilibriumFromEventFlow (nashEquilibriumToEventFlow x) =
        nashEquilibriumFromEventFlow (nashEquilibriumToEventFlow y) :=
    congrArg nashEquilibriumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NashEquilibriumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NashEquilibriumTasteGate_single_carrier_alignment_round_trip y)))

private theorem NashEquilibriumTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : NashEquilibriumUp, nashEquilibriumFields x = nashEquilibriumFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P₁ S₁ A₁ U₁ B₁ E₁ H₁ C₁ Q₁ N₁ =>
      cases y with
      | mk P₂ S₂ A₂ U₂ B₂ E₂ H₂ C₂ Q₂ N₂ =>
          cases hfields
          rfl

instance nashEquilibriumBHistCarrier : BHistCarrier NashEquilibriumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nashEquilibriumToEventFlow
  fromEventFlow := nashEquilibriumFromEventFlow

instance nashEquilibriumChapterTasteGate : ChapterTasteGate NashEquilibriumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nashEquilibriumFromEventFlow (nashEquilibriumToEventFlow x) = some x
    exact NashEquilibriumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NashEquilibriumTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance nashEquilibriumFieldFaithful : FieldFaithful NashEquilibriumUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := nashEquilibriumFields
  field_faithful := NashEquilibriumTasteGate_single_carrier_alignment_fields_faithful

theorem NashEquilibriumTasteGate_single_carrier_alignment :
    (forall h : BHist, nashEquilibriumDecodeBHist (nashEquilibriumEncodeBHist h) = h) ∧
      (forall x : NashEquilibriumUp, nashEquilibriumFromEventFlow (nashEquilibriumToEventFlow x) = some x) ∧
        (forall x y : NashEquilibriumUp, nashEquilibriumToEventFlow x = nashEquilibriumToEventFlow y -> x = y) ∧
          nashEquilibriumEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨NashEquilibriumTasteGate_single_carrier_alignment_decode_encode,
      NashEquilibriumTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        NashEquilibriumTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.NashEquilibriumUp
