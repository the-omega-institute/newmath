import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LipschitzContinuityHandoffUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LipschitzContinuityHandoffUp : Type where
  | mk (L X Y G B U Q R H C P N : BHist) : LipschitzContinuityHandoffUp
  deriving DecidableEq

def lipschitzContinuityHandoffEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lipschitzContinuityHandoffEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lipschitzContinuityHandoffEncodeBHist h

def lipschitzContinuityHandoffDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lipschitzContinuityHandoffDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lipschitzContinuityHandoffDecodeBHist tail)

private theorem LipschitzContinuityHandoffTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      lipschitzContinuityHandoffDecodeBHist
        (lipschitzContinuityHandoffEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lipschitzContinuityHandoffFields :
    LipschitzContinuityHandoffUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LipschitzContinuityHandoffUp.mk L X Y G B U Q R H C P N =>
      [L, X, Y, G, B, U, Q, R, H, C, P, N]

def lipschitzContinuityHandoffToEventFlow :
    LipschitzContinuityHandoffUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lipschitzContinuityHandoffFields x).map lipschitzContinuityHandoffEncodeBHist

private def lipschitzContinuityHandoffRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => lipschitzContinuityHandoffRawAt n rest

def lipschitzContinuityHandoffFromEventFlow
    (flow : EventFlow) : Option LipschitzContinuityHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LipschitzContinuityHandoffUp.mk
      (lipschitzContinuityHandoffDecodeBHist (lipschitzContinuityHandoffRawAt 0 flow))
      (lipschitzContinuityHandoffDecodeBHist (lipschitzContinuityHandoffRawAt 1 flow))
      (lipschitzContinuityHandoffDecodeBHist (lipschitzContinuityHandoffRawAt 2 flow))
      (lipschitzContinuityHandoffDecodeBHist (lipschitzContinuityHandoffRawAt 3 flow))
      (lipschitzContinuityHandoffDecodeBHist (lipschitzContinuityHandoffRawAt 4 flow))
      (lipschitzContinuityHandoffDecodeBHist (lipschitzContinuityHandoffRawAt 5 flow))
      (lipschitzContinuityHandoffDecodeBHist (lipschitzContinuityHandoffRawAt 6 flow))
      (lipschitzContinuityHandoffDecodeBHist (lipschitzContinuityHandoffRawAt 7 flow))
      (lipschitzContinuityHandoffDecodeBHist (lipschitzContinuityHandoffRawAt 8 flow))
      (lipschitzContinuityHandoffDecodeBHist (lipschitzContinuityHandoffRawAt 9 flow))
      (lipschitzContinuityHandoffDecodeBHist (lipschitzContinuityHandoffRawAt 10 flow))
      (lipschitzContinuityHandoffDecodeBHist (lipschitzContinuityHandoffRawAt 11 flow)))

private theorem LipschitzContinuityHandoffTasteGate_single_carrier_alignment_round_trip
    (x : LipschitzContinuityHandoffUp) :
    lipschitzContinuityHandoffFromEventFlow
      (lipschitzContinuityHandoffToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L X Y G B U Q R H C P N =>
      change
        some
          (LipschitzContinuityHandoffUp.mk
            (lipschitzContinuityHandoffDecodeBHist
              (lipschitzContinuityHandoffEncodeBHist L))
            (lipschitzContinuityHandoffDecodeBHist
              (lipschitzContinuityHandoffEncodeBHist X))
            (lipschitzContinuityHandoffDecodeBHist
              (lipschitzContinuityHandoffEncodeBHist Y))
            (lipschitzContinuityHandoffDecodeBHist
              (lipschitzContinuityHandoffEncodeBHist G))
            (lipschitzContinuityHandoffDecodeBHist
              (lipschitzContinuityHandoffEncodeBHist B))
            (lipschitzContinuityHandoffDecodeBHist
              (lipschitzContinuityHandoffEncodeBHist U))
            (lipschitzContinuityHandoffDecodeBHist
              (lipschitzContinuityHandoffEncodeBHist Q))
            (lipschitzContinuityHandoffDecodeBHist
              (lipschitzContinuityHandoffEncodeBHist R))
            (lipschitzContinuityHandoffDecodeBHist
              (lipschitzContinuityHandoffEncodeBHist H))
            (lipschitzContinuityHandoffDecodeBHist
              (lipschitzContinuityHandoffEncodeBHist C))
            (lipschitzContinuityHandoffDecodeBHist
              (lipschitzContinuityHandoffEncodeBHist P))
            (lipschitzContinuityHandoffDecodeBHist
              (lipschitzContinuityHandoffEncodeBHist N))) =
          some (LipschitzContinuityHandoffUp.mk L X Y G B U Q R H C P N)
      rw [LipschitzContinuityHandoffTasteGate_single_carrier_alignment_decode_encode L,
        LipschitzContinuityHandoffTasteGate_single_carrier_alignment_decode_encode X,
        LipschitzContinuityHandoffTasteGate_single_carrier_alignment_decode_encode Y,
        LipschitzContinuityHandoffTasteGate_single_carrier_alignment_decode_encode G,
        LipschitzContinuityHandoffTasteGate_single_carrier_alignment_decode_encode B,
        LipschitzContinuityHandoffTasteGate_single_carrier_alignment_decode_encode U,
        LipschitzContinuityHandoffTasteGate_single_carrier_alignment_decode_encode Q,
        LipschitzContinuityHandoffTasteGate_single_carrier_alignment_decode_encode R,
        LipschitzContinuityHandoffTasteGate_single_carrier_alignment_decode_encode H,
        LipschitzContinuityHandoffTasteGate_single_carrier_alignment_decode_encode C,
        LipschitzContinuityHandoffTasteGate_single_carrier_alignment_decode_encode P,
        LipschitzContinuityHandoffTasteGate_single_carrier_alignment_decode_encode N]

private theorem LipschitzContinuityHandoffTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LipschitzContinuityHandoffUp} :
    lipschitzContinuityHandoffToEventFlow x =
      lipschitzContinuityHandoffToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lipschitzContinuityHandoffFromEventFlow
          (lipschitzContinuityHandoffToEventFlow x) =
        lipschitzContinuityHandoffFromEventFlow
          (lipschitzContinuityHandoffToEventFlow y) :=
    congrArg lipschitzContinuityHandoffFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LipschitzContinuityHandoffTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LipschitzContinuityHandoffTasteGate_single_carrier_alignment_round_trip y)))

private theorem LipschitzContinuityHandoffTasteGate_single_carrier_alignment_fields :
    ∀ x y : LipschitzContinuityHandoffUp,
      lipschitzContinuityHandoffFields x = lipschitzContinuityHandoffFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ X₁ Y₁ G₁ B₁ U₁ Q₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ X₂ Y₂ G₂ B₂ U₂ Q₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance lipschitzContinuityHandoffBHistCarrier :
    BHistCarrier LipschitzContinuityHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lipschitzContinuityHandoffToEventFlow
  fromEventFlow := lipschitzContinuityHandoffFromEventFlow

instance lipschitzContinuityHandoffChapterTasteGate :
    ChapterTasteGate LipschitzContinuityHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lipschitzContinuityHandoffFromEventFlow
      (lipschitzContinuityHandoffToEventFlow x) = some x
    exact LipschitzContinuityHandoffTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LipschitzContinuityHandoffTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance lipschitzContinuityHandoffFieldFaithful :
    FieldFaithful LipschitzContinuityHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := lipschitzContinuityHandoffFields
  field_faithful := LipschitzContinuityHandoffTasteGate_single_carrier_alignment_fields

instance lipschitzContinuityHandoffNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LipschitzContinuityHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LipschitzContinuityHandoffUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      LipschitzContinuityHandoffUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LipschitzContinuityHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lipschitzContinuityHandoffChapterTasteGate

theorem LipschitzContinuityHandoffTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LipschitzContinuityHandoffUp) ∧
      Nonempty (FieldFaithful LipschitzContinuityHandoffUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial LipschitzContinuityHandoffUp) ∧
      (∀ h : BHist,
        lipschitzContinuityHandoffDecodeBHist
          (lipschitzContinuityHandoffEncodeBHist h) = h) ∧
      (∀ x : LipschitzContinuityHandoffUp,
        lipschitzContinuityHandoffFromEventFlow
          (lipschitzContinuityHandoffToEventFlow x) = some x) ∧
      (∀ x y : LipschitzContinuityHandoffUp,
        lipschitzContinuityHandoffToEventFlow x =
          lipschitzContinuityHandoffToEventFlow y → x = y) ∧
      lipschitzContinuityHandoffEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨lipschitzContinuityHandoffChapterTasteGate⟩,
      ⟨lipschitzContinuityHandoffFieldFaithful⟩,
      ⟨lipschitzContinuityHandoffNontrivial⟩,
      LipschitzContinuityHandoffTasteGate_single_carrier_alignment_decode_encode,
      LipschitzContinuityHandoffTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        LipschitzContinuityHandoffTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LipschitzContinuityHandoffUp
