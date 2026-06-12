import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SierpinskiCarpetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SierpinskiCarpetUp : Type where
  | mk (G D W Q E H C P N : BHist) : SierpinskiCarpetUp
  deriving DecidableEq

def sierpinskiCarpetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sierpinskiCarpetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sierpinskiCarpetEncodeBHist h

def sierpinskiCarpetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sierpinskiCarpetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sierpinskiCarpetDecodeBHist tail)

private theorem SierpinskiCarpetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, sierpinskiCarpetDecodeBHist (sierpinskiCarpetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def sierpinskiCarpetFields : SierpinskiCarpetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SierpinskiCarpetUp.mk G D W Q E H C P N => [G, D, W, Q, E, H, C, P, N]

def sierpinskiCarpetToEventFlow : SierpinskiCarpetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sierpinskiCarpetFields x).map sierpinskiCarpetEncodeBHist

private def SierpinskiCarpetTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      SierpinskiCarpetTasteGate_single_carrier_alignment_eventAt index rest

def sierpinskiCarpetFromEventFlow (ef : EventFlow) : Option SierpinskiCarpetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SierpinskiCarpetUp.mk
      (sierpinskiCarpetDecodeBHist
        (SierpinskiCarpetTasteGate_single_carrier_alignment_eventAt 0 ef))
      (sierpinskiCarpetDecodeBHist
        (SierpinskiCarpetTasteGate_single_carrier_alignment_eventAt 1 ef))
      (sierpinskiCarpetDecodeBHist
        (SierpinskiCarpetTasteGate_single_carrier_alignment_eventAt 2 ef))
      (sierpinskiCarpetDecodeBHist
        (SierpinskiCarpetTasteGate_single_carrier_alignment_eventAt 3 ef))
      (sierpinskiCarpetDecodeBHist
        (SierpinskiCarpetTasteGate_single_carrier_alignment_eventAt 4 ef))
      (sierpinskiCarpetDecodeBHist
        (SierpinskiCarpetTasteGate_single_carrier_alignment_eventAt 5 ef))
      (sierpinskiCarpetDecodeBHist
        (SierpinskiCarpetTasteGate_single_carrier_alignment_eventAt 6 ef))
      (sierpinskiCarpetDecodeBHist
        (SierpinskiCarpetTasteGate_single_carrier_alignment_eventAt 7 ef))
      (sierpinskiCarpetDecodeBHist
        (SierpinskiCarpetTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem SierpinskiCarpetTasteGate_single_carrier_alignment_round_trip
    (x : SierpinskiCarpetUp) :
    sierpinskiCarpetFromEventFlow (sierpinskiCarpetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk G D W Q E H C P N =>
      change
        some
          (SierpinskiCarpetUp.mk
            (sierpinskiCarpetDecodeBHist (sierpinskiCarpetEncodeBHist G))
            (sierpinskiCarpetDecodeBHist (sierpinskiCarpetEncodeBHist D))
            (sierpinskiCarpetDecodeBHist (sierpinskiCarpetEncodeBHist W))
            (sierpinskiCarpetDecodeBHist (sierpinskiCarpetEncodeBHist Q))
            (sierpinskiCarpetDecodeBHist (sierpinskiCarpetEncodeBHist E))
            (sierpinskiCarpetDecodeBHist (sierpinskiCarpetEncodeBHist H))
            (sierpinskiCarpetDecodeBHist (sierpinskiCarpetEncodeBHist C))
            (sierpinskiCarpetDecodeBHist (sierpinskiCarpetEncodeBHist P))
            (sierpinskiCarpetDecodeBHist (sierpinskiCarpetEncodeBHist N))) =
          some (SierpinskiCarpetUp.mk G D W Q E H C P N)
      rw [SierpinskiCarpetTasteGate_single_carrier_alignment_decode_encode G,
        SierpinskiCarpetTasteGate_single_carrier_alignment_decode_encode D,
        SierpinskiCarpetTasteGate_single_carrier_alignment_decode_encode W,
        SierpinskiCarpetTasteGate_single_carrier_alignment_decode_encode Q,
        SierpinskiCarpetTasteGate_single_carrier_alignment_decode_encode E,
        SierpinskiCarpetTasteGate_single_carrier_alignment_decode_encode H,
        SierpinskiCarpetTasteGate_single_carrier_alignment_decode_encode C,
        SierpinskiCarpetTasteGate_single_carrier_alignment_decode_encode P,
        SierpinskiCarpetTasteGate_single_carrier_alignment_decode_encode N]

private theorem SierpinskiCarpetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SierpinskiCarpetUp} :
    sierpinskiCarpetToEventFlow x = sierpinskiCarpetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sierpinskiCarpetFromEventFlow (sierpinskiCarpetToEventFlow x) =
        sierpinskiCarpetFromEventFlow (sierpinskiCarpetToEventFlow y) :=
    congrArg sierpinskiCarpetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SierpinskiCarpetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SierpinskiCarpetTasteGate_single_carrier_alignment_round_trip y)))

private theorem SierpinskiCarpetTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : SierpinskiCarpetUp, sierpinskiCarpetFields x = sierpinskiCarpetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G₁ D₁ W₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk G₂ D₂ W₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance sierpinskiCarpetBHistCarrier : BHistCarrier SierpinskiCarpetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sierpinskiCarpetToEventFlow
  fromEventFlow := sierpinskiCarpetFromEventFlow

instance sierpinskiCarpetChapterTasteGate : ChapterTasteGate SierpinskiCarpetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sierpinskiCarpetFromEventFlow (sierpinskiCarpetToEventFlow x) = some x
    exact SierpinskiCarpetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SierpinskiCarpetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance sierpinskiCarpetFieldFaithful : FieldFaithful SierpinskiCarpetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sierpinskiCarpetFields
  field_faithful := SierpinskiCarpetTasteGate_single_carrier_alignment_fields_faithful

instance sierpinskiCarpetNontrivial : BEDC.Meta.TasteGate.Nontrivial SierpinskiCarpetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SierpinskiCarpetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SierpinskiCarpetUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SierpinskiCarpetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sierpinskiCarpetChapterTasteGate

theorem SierpinskiCarpetTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SierpinskiCarpetUp) ∧
      Nonempty (FieldFaithful SierpinskiCarpetUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial SierpinskiCarpetUp) ∧
          (∀ h : BHist, sierpinskiCarpetDecodeBHist (sierpinskiCarpetEncodeBHist h) = h) ∧
            (∀ x : SierpinskiCarpetUp,
              sierpinskiCarpetFromEventFlow (sierpinskiCarpetToEventFlow x) = some x) ∧
              (∀ x y : SierpinskiCarpetUp,
                sierpinskiCarpetToEventFlow x = sierpinskiCarpetToEventFlow y → x = y) ∧
                sierpinskiCarpetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨sierpinskiCarpetChapterTasteGate⟩,
      ⟨sierpinskiCarpetFieldFaithful⟩,
      ⟨sierpinskiCarpetNontrivial⟩,
      SierpinskiCarpetTasteGate_single_carrier_alignment_decode_encode,
      SierpinskiCarpetTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => SierpinskiCarpetTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SierpinskiCarpetUp
