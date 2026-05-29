import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparatedCompletionReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeparatedCompletionReflectionUp : Type where
  | mk (M S C E Z H K P N : BHist) : SeparatedCompletionReflectionUp
  deriving DecidableEq

def separatedCompletionReflectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: separatedCompletionReflectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: separatedCompletionReflectionEncodeBHist h

def separatedCompletionReflectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separatedCompletionReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separatedCompletionReflectionDecodeBHist tail)

private theorem SeparatedCompletionReflectionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      separatedCompletionReflectionDecodeBHist
        (separatedCompletionReflectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def separatedCompletionReflectionFields : SeparatedCompletionReflectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeparatedCompletionReflectionUp.mk M S C E Z H K P N => [M, S, C, E, Z, H, K, P, N]

def separatedCompletionReflectionToEventFlow :
    SeparatedCompletionReflectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (separatedCompletionReflectionFields x).map separatedCompletionReflectionEncodeBHist

private def separatedCompletionReflectionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => separatedCompletionReflectionRawAt n rest

def separatedCompletionReflectionFromEventFlow
    (flow : EventFlow) : Option SeparatedCompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SeparatedCompletionReflectionUp.mk
      (separatedCompletionReflectionDecodeBHist (separatedCompletionReflectionRawAt 0 flow))
      (separatedCompletionReflectionDecodeBHist (separatedCompletionReflectionRawAt 1 flow))
      (separatedCompletionReflectionDecodeBHist (separatedCompletionReflectionRawAt 2 flow))
      (separatedCompletionReflectionDecodeBHist (separatedCompletionReflectionRawAt 3 flow))
      (separatedCompletionReflectionDecodeBHist (separatedCompletionReflectionRawAt 4 flow))
      (separatedCompletionReflectionDecodeBHist (separatedCompletionReflectionRawAt 5 flow))
      (separatedCompletionReflectionDecodeBHist (separatedCompletionReflectionRawAt 6 flow))
      (separatedCompletionReflectionDecodeBHist (separatedCompletionReflectionRawAt 7 flow))
      (separatedCompletionReflectionDecodeBHist (separatedCompletionReflectionRawAt 8 flow)))

private theorem SeparatedCompletionReflectionTasteGate_single_carrier_alignment_round_trip
    (x : SeparatedCompletionReflectionUp) :
    separatedCompletionReflectionFromEventFlow
      (separatedCompletionReflectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M S C E Z H K P N =>
      change
        some
          (SeparatedCompletionReflectionUp.mk
            (separatedCompletionReflectionDecodeBHist
              (separatedCompletionReflectionEncodeBHist M))
            (separatedCompletionReflectionDecodeBHist
              (separatedCompletionReflectionEncodeBHist S))
            (separatedCompletionReflectionDecodeBHist
              (separatedCompletionReflectionEncodeBHist C))
            (separatedCompletionReflectionDecodeBHist
              (separatedCompletionReflectionEncodeBHist E))
            (separatedCompletionReflectionDecodeBHist
              (separatedCompletionReflectionEncodeBHist Z))
            (separatedCompletionReflectionDecodeBHist
              (separatedCompletionReflectionEncodeBHist H))
            (separatedCompletionReflectionDecodeBHist
              (separatedCompletionReflectionEncodeBHist K))
            (separatedCompletionReflectionDecodeBHist
              (separatedCompletionReflectionEncodeBHist P))
            (separatedCompletionReflectionDecodeBHist
              (separatedCompletionReflectionEncodeBHist N))) =
          some (SeparatedCompletionReflectionUp.mk M S C E Z H K P N)
      rw [SeparatedCompletionReflectionTasteGate_single_carrier_alignment_decode_encode M,
        SeparatedCompletionReflectionTasteGate_single_carrier_alignment_decode_encode S,
        SeparatedCompletionReflectionTasteGate_single_carrier_alignment_decode_encode C,
        SeparatedCompletionReflectionTasteGate_single_carrier_alignment_decode_encode E,
        SeparatedCompletionReflectionTasteGate_single_carrier_alignment_decode_encode Z,
        SeparatedCompletionReflectionTasteGate_single_carrier_alignment_decode_encode H,
        SeparatedCompletionReflectionTasteGate_single_carrier_alignment_decode_encode K,
        SeparatedCompletionReflectionTasteGate_single_carrier_alignment_decode_encode P,
        SeparatedCompletionReflectionTasteGate_single_carrier_alignment_decode_encode N]

private theorem SeparatedCompletionReflectionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SeparatedCompletionReflectionUp} :
    separatedCompletionReflectionToEventFlow x =
      separatedCompletionReflectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separatedCompletionReflectionFromEventFlow
          (separatedCompletionReflectionToEventFlow x) =
        separatedCompletionReflectionFromEventFlow
          (separatedCompletionReflectionToEventFlow y) :=
    congrArg separatedCompletionReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SeparatedCompletionReflectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SeparatedCompletionReflectionTasteGate_single_carrier_alignment_round_trip y)))

private theorem SeparatedCompletionReflectionTasteGate_single_carrier_alignment_fields :
    ∀ x y : SeparatedCompletionReflectionUp,
      separatedCompletionReflectionFields x = separatedCompletionReflectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ S₁ C₁ E₁ Z₁ H₁ K₁ P₁ N₁ =>
      cases y with
      | mk M₂ S₂ C₂ E₂ Z₂ H₂ K₂ P₂ N₂ =>
          cases hfields
          rfl

instance separatedCompletionReflectionBHistCarrier :
    BHistCarrier SeparatedCompletionReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separatedCompletionReflectionToEventFlow
  fromEventFlow := separatedCompletionReflectionFromEventFlow

instance separatedCompletionReflectionChapterTasteGate :
    ChapterTasteGate SeparatedCompletionReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change separatedCompletionReflectionFromEventFlow
      (separatedCompletionReflectionToEventFlow x) = some x
    exact SeparatedCompletionReflectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SeparatedCompletionReflectionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance separatedCompletionReflectionFieldFaithful :
    FieldFaithful SeparatedCompletionReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := separatedCompletionReflectionFields
  field_faithful := SeparatedCompletionReflectionTasteGate_single_carrier_alignment_fields

instance separatedCompletionReflectionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial SeparatedCompletionReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SeparatedCompletionReflectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SeparatedCompletionReflectionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SeparatedCompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  separatedCompletionReflectionChapterTasteGate

theorem SeparatedCompletionReflectionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SeparatedCompletionReflectionUp) ∧
      Nonempty (FieldFaithful SeparatedCompletionReflectionUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial SeparatedCompletionReflectionUp) ∧
      (∀ h : BHist,
        separatedCompletionReflectionDecodeBHist
          (separatedCompletionReflectionEncodeBHist h) = h) ∧
      (∀ x : SeparatedCompletionReflectionUp,
        separatedCompletionReflectionFromEventFlow
          (separatedCompletionReflectionToEventFlow x) = some x) ∧
      (∀ x y : SeparatedCompletionReflectionUp,
        separatedCompletionReflectionToEventFlow x =
          separatedCompletionReflectionToEventFlow y → x = y) ∧
      separatedCompletionReflectionEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨separatedCompletionReflectionChapterTasteGate⟩,
      ⟨separatedCompletionReflectionFieldFaithful⟩,
      ⟨separatedCompletionReflectionNontrivial⟩,
      SeparatedCompletionReflectionTasteGate_single_carrier_alignment_decode_encode,
      SeparatedCompletionReflectionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        SeparatedCompletionReflectionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SeparatedCompletionReflectionUp
