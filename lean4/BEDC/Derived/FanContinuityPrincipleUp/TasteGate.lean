import BEDC.Derived.FanContinuityPrincipleUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FanContinuityPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def fanContinuityPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fanContinuityPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fanContinuityPrincipleEncodeBHist h

def fanContinuityPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fanContinuityPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fanContinuityPrincipleDecodeBHist tail)

private theorem fanContinuityPrinciple_decode_encode_bhist :
    ∀ h : BHist,
      fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fanContinuityPrincipleFields : FanContinuityPrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FanContinuityPrincipleUp.mk B A Q S R E H C P N => [B, A, Q, S, R, E, H, C, P, N]

def fanContinuityPrincipleToEventFlow : FanContinuityPrincipleUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (fanContinuityPrincipleFields x).map fanContinuityPrincipleEncodeBHist

private def fanContinuityPrincipleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fanContinuityPrincipleEventAtDefault index rest

def fanContinuityPrincipleFromEventFlow
    (ef : EventFlow) : Option FanContinuityPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FanContinuityPrincipleUp.mk
      (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEventAtDefault 0 ef))
      (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEventAtDefault 1 ef))
      (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEventAtDefault 2 ef))
      (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEventAtDefault 3 ef))
      (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEventAtDefault 4 ef))
      (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEventAtDefault 5 ef))
      (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEventAtDefault 6 ef))
      (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEventAtDefault 7 ef))
      (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEventAtDefault 8 ef))
      (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEventAtDefault 9 ef)))

private theorem fanContinuityPrinciple_round_trip :
    ∀ x : FanContinuityPrincipleUp,
      fanContinuityPrincipleFromEventFlow (fanContinuityPrincipleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B A Q S R E H C P N =>
      change
        some
          (FanContinuityPrincipleUp.mk
            (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEncodeBHist B))
            (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEncodeBHist A))
            (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEncodeBHist Q))
            (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEncodeBHist S))
            (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEncodeBHist R))
            (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEncodeBHist E))
            (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEncodeBHist H))
            (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEncodeBHist C))
            (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEncodeBHist P))
            (fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEncodeBHist N))) =
          some (FanContinuityPrincipleUp.mk B A Q S R E H C P N)
      rw [fanContinuityPrinciple_decode_encode_bhist B,
        fanContinuityPrinciple_decode_encode_bhist A,
        fanContinuityPrinciple_decode_encode_bhist Q,
        fanContinuityPrinciple_decode_encode_bhist S,
        fanContinuityPrinciple_decode_encode_bhist R,
        fanContinuityPrinciple_decode_encode_bhist E,
        fanContinuityPrinciple_decode_encode_bhist H,
        fanContinuityPrinciple_decode_encode_bhist C,
        fanContinuityPrinciple_decode_encode_bhist P,
        fanContinuityPrinciple_decode_encode_bhist N]

private theorem fanContinuityPrincipleToEventFlow_injective
    {x y : FanContinuityPrincipleUp} :
    fanContinuityPrincipleToEventFlow x = fanContinuityPrincipleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fanContinuityPrincipleFromEventFlow (fanContinuityPrincipleToEventFlow x) =
        fanContinuityPrincipleFromEventFlow (fanContinuityPrincipleToEventFlow y) :=
    congrArg fanContinuityPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fanContinuityPrinciple_round_trip x).symm
      (Eq.trans hread (fanContinuityPrinciple_round_trip y)))

private theorem fanContinuityPrinciple_field_faithful :
    ∀ x y : FanContinuityPrincipleUp,
      fanContinuityPrincipleFields x = fanContinuityPrincipleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B A Q S R E H C P N =>
      cases y with
      | mk B' A' Q' S' R' E' H' C' P' N' =>
          cases hfields
          rfl

instance fanContinuityPrincipleBHistCarrier : BHistCarrier FanContinuityPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fanContinuityPrincipleToEventFlow
  fromEventFlow := fanContinuityPrincipleFromEventFlow

instance fanContinuityPrincipleChapterTasteGate :
    ChapterTasteGate FanContinuityPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fanContinuityPrincipleFromEventFlow (fanContinuityPrincipleToEventFlow x) = some x
    exact fanContinuityPrinciple_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fanContinuityPrincipleToEventFlow_injective heq)

instance fanContinuityPrincipleFieldFaithful : FieldFaithful FanContinuityPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fanContinuityPrincipleFields
  field_faithful := fanContinuityPrinciple_field_faithful

instance fanContinuityPrincipleNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FanContinuityPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FanContinuityPrincipleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FanContinuityPrincipleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FanContinuityPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fanContinuityPrincipleChapterTasteGate

theorem FanContinuityPrincipleTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FanContinuityPrincipleUp) ∧
      Nonempty (FieldFaithful FanContinuityPrincipleUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial FanContinuityPrincipleUp) ∧
      (∀ h : BHist,
        fanContinuityPrincipleDecodeBHist (fanContinuityPrincipleEncodeBHist h) = h) ∧
      (∀ x : FanContinuityPrincipleUp,
        fanContinuityPrincipleFromEventFlow (fanContinuityPrincipleToEventFlow x) = some x) ∧
      (∀ x y : FanContinuityPrincipleUp,
        fanContinuityPrincipleToEventFlow x = fanContinuityPrincipleToEventFlow y → x = y) ∧
      fanContinuityPrincipleEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨fanContinuityPrincipleChapterTasteGate⟩, ⟨fanContinuityPrincipleFieldFaithful⟩,
      ⟨fanContinuityPrincipleNontrivial⟩, fanContinuityPrinciple_decode_encode_bhist,
      fanContinuityPrinciple_round_trip,
      (fun _ _ heq => fanContinuityPrincipleToEventFlow_injective heq), rfl⟩

end BEDC.Derived.FanContinuityPrincipleUp
