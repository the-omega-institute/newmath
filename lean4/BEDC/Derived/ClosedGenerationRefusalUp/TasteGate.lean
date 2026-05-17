import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedGenerationRefusalUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedGenerationRefusalUp : Type where
  | mk (P T G R I H C Q N : BHist) : ClosedGenerationRefusalUp
  deriving DecidableEq

def closedGenerationRefusalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedGenerationRefusalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedGenerationRefusalEncodeBHist h

def closedGenerationRefusalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedGenerationRefusalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedGenerationRefusalDecodeBHist tail)

private theorem closedGenerationRefusalDecode_encode_bhist :
    ∀ h : BHist,
      closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def closedGenerationRefusalFields : ClosedGenerationRefusalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedGenerationRefusalUp.mk P T G R I H C Q N => [P, T, G, R, I, H, C, Q, N]

def closedGenerationRefusalToEventFlow : ClosedGenerationRefusalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedGenerationRefusalUp.mk P T G R I H C Q N =>
      [[BMark.b0],
        closedGenerationRefusalEncodeBHist P,
        [BMark.b1, BMark.b0],
        closedGenerationRefusalEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        closedGenerationRefusalEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedGenerationRefusalEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedGenerationRefusalEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedGenerationRefusalEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedGenerationRefusalEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closedGenerationRefusalEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closedGenerationRefusalEncodeBHist N]

private def closedGenerationRefusalRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => closedGenerationRefusalRawAt n rest

private def closedGenerationRefusalLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => closedGenerationRefusalLengthEq n rest

def closedGenerationRefusalFromEventFlow : EventFlow → Option ClosedGenerationRefusalUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match closedGenerationRefusalLengthEq 18 flow with
      | true =>
          some
            (ClosedGenerationRefusalUp.mk
              (closedGenerationRefusalDecodeBHist (closedGenerationRefusalRawAt 1 flow))
              (closedGenerationRefusalDecodeBHist (closedGenerationRefusalRawAt 3 flow))
              (closedGenerationRefusalDecodeBHist (closedGenerationRefusalRawAt 5 flow))
              (closedGenerationRefusalDecodeBHist (closedGenerationRefusalRawAt 7 flow))
              (closedGenerationRefusalDecodeBHist (closedGenerationRefusalRawAt 9 flow))
              (closedGenerationRefusalDecodeBHist (closedGenerationRefusalRawAt 11 flow))
              (closedGenerationRefusalDecodeBHist (closedGenerationRefusalRawAt 13 flow))
              (closedGenerationRefusalDecodeBHist (closedGenerationRefusalRawAt 15 flow))
              (closedGenerationRefusalDecodeBHist (closedGenerationRefusalRawAt 17 flow)))
      | false => none

private theorem closedGenerationRefusal_round_trip :
    ∀ x : ClosedGenerationRefusalUp,
      closedGenerationRefusalFromEventFlow
        (closedGenerationRefusalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P T G R I H C Q N =>
      change
        some
          (ClosedGenerationRefusalUp.mk
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist P))
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist T))
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist G))
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist R))
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist I))
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist H))
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist C))
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist Q))
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist N))) =
          some (ClosedGenerationRefusalUp.mk P T G R I H C Q N)
      rw [closedGenerationRefusalDecode_encode_bhist P,
        closedGenerationRefusalDecode_encode_bhist T,
        closedGenerationRefusalDecode_encode_bhist G,
        closedGenerationRefusalDecode_encode_bhist R,
        closedGenerationRefusalDecode_encode_bhist I,
        closedGenerationRefusalDecode_encode_bhist H,
        closedGenerationRefusalDecode_encode_bhist C,
        closedGenerationRefusalDecode_encode_bhist Q,
        closedGenerationRefusalDecode_encode_bhist N]

private theorem closedGenerationRefusalToEventFlow_injective
    {x y : ClosedGenerationRefusalUp} :
    closedGenerationRefusalToEventFlow x = closedGenerationRefusalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedGenerationRefusalFromEventFlow
          (closedGenerationRefusalToEventFlow x) =
        closedGenerationRefusalFromEventFlow
          (closedGenerationRefusalToEventFlow y) :=
    congrArg closedGenerationRefusalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedGenerationRefusal_round_trip x).symm
      (Eq.trans hread (closedGenerationRefusal_round_trip y)))

private theorem closedGenerationRefusal_field_faithful :
    ∀ x y : ClosedGenerationRefusalUp,
      closedGenerationRefusalFields x = closedGenerationRefusalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P1 T1 G1 R1 I1 H1 C1 Q1 N1 =>
      cases y with
      | mk P2 T2 G2 R2 I2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance closedGenerationRefusalBHistCarrier : BHistCarrier ClosedGenerationRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedGenerationRefusalToEventFlow
  fromEventFlow := closedGenerationRefusalFromEventFlow

instance closedGenerationRefusalChapterTasteGate :
    ChapterTasteGate ClosedGenerationRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedGenerationRefusalFromEventFlow
        (closedGenerationRefusalToEventFlow x) = some x
    exact closedGenerationRefusal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedGenerationRefusalToEventFlow_injective heq)

instance closedGenerationRefusalFieldFaithful :
    FieldFaithful ClosedGenerationRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedGenerationRefusalFields
  field_faithful := closedGenerationRefusal_field_faithful

instance closedGenerationRefusalNontrivial : Nontrivial ClosedGenerationRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedGenerationRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedGenerationRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClosedGenerationRefusalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedGenerationRefusalChapterTasteGate

theorem closedGenerationRefusalTasteGate_single_carrier_alignment :
    closedGenerationRefusalEncodeBHist BHist.Empty = [] ∧
      (∀ h : BHist,
        closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist h) = h) ∧
        (∀ x : ClosedGenerationRefusalUp,
          closedGenerationRefusalFromEventFlow (closedGenerationRefusalToEventFlow x) =
            some x) ∧
          (∀ x y : ClosedGenerationRefusalUp,
            closedGenerationRefusalToEventFlow x = closedGenerationRefusalToEventFlow y →
              x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨rfl, closedGenerationRefusalDecode_encode_bhist, closedGenerationRefusal_round_trip,
      fun _ _ heq => closedGenerationRefusalToEventFlow_injective heq⟩

end BEDC.Derived.ClosedGenerationRefusalUp.TasteGate
