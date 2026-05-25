import BEDC.Derived.CauchySpeedupUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySpeedupUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate
open BEDC.Derived

def cauchySpeedupEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySpeedupEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySpeedupEncodeBHist h

def cauchySpeedupDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySpeedupDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySpeedupDecodeBHist tail)

private theorem CauchySpeedupTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySpeedupFields : CauchySpeedupUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySpeedupUp.mk A J D W R E H C P N => [A, J, D, W, R, E, H, C, P, N]

def cauchySpeedupToEventFlow : CauchySpeedupUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySpeedupFields x).map cauchySpeedupEncodeBHist

private def cauchySpeedupEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySpeedupEventAt index rest

def cauchySpeedupFromEventFlow : EventFlow → Option CauchySpeedupUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CauchySpeedupUp.mk
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 0 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 1 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 2 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 3 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 4 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 5 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 6 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 7 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 8 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 9 ef)))

private theorem CauchySpeedupTasteGate_single_carrier_alignment_round_trip
    (x : CauchySpeedupUp) :
    cauchySpeedupFromEventFlow (cauchySpeedupToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A J D W R E H C P N =>
      change
        some
          (CauchySpeedupUp.mk
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist A))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist J))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist D))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist W))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist R))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist E))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist H))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist C))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist P))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist N))) =
          some (CauchySpeedupUp.mk A J D W R E H C P N)
      rw [CauchySpeedupTasteGate_single_carrier_alignment_decode_encode A,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode J,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode D,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode W,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode R,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode E,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode H,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode C,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode P,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchySpeedupTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchySpeedupUp} :
    cauchySpeedupToEventFlow x = cauchySpeedupToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySpeedupFromEventFlow (cauchySpeedupToEventFlow x) =
        cauchySpeedupFromEventFlow (cauchySpeedupToEventFlow y) :=
    congrArg cauchySpeedupFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchySpeedupTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchySpeedupTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchySpeedupTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchySpeedupUp, cauchySpeedupFields x = cauchySpeedupFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ J₁ D₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ J₂ D₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchySpeedupBHistCarrier : BHistCarrier CauchySpeedupUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySpeedupToEventFlow
  fromEventFlow := cauchySpeedupFromEventFlow

instance cauchySpeedupChapterTasteGate : ChapterTasteGate CauchySpeedupUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySpeedupFromEventFlow (cauchySpeedupToEventFlow x) = some x
    exact CauchySpeedupTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchySpeedupTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchySpeedupFieldFaithful : FieldFaithful CauchySpeedupUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchySpeedupFields
  field_faithful := CauchySpeedupTasteGate_single_carrier_alignment_fields_faithful

instance cauchySpeedupNontrivial : BEDC.Meta.TasteGate.Nontrivial CauchySpeedupUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchySpeedupUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchySpeedupUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CauchySpeedupTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchySpeedupUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySpeedupChapterTasteGate

theorem CauchySpeedupTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchySpeedupUp) ∧
      Nonempty (FieldFaithful CauchySpeedupUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchySpeedupUp) ∧
          (∀ h : BHist, cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist h) = h) ∧
            (∀ x : CauchySpeedupUp,
              cauchySpeedupFromEventFlow (cauchySpeedupToEventFlow x) = some x) ∧
              cauchySpeedupEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨cauchySpeedupChapterTasteGate⟩, ⟨cauchySpeedupFieldFaithful⟩,
      ⟨cauchySpeedupNontrivial⟩,
      CauchySpeedupTasteGate_single_carrier_alignment_decode_encode,
      CauchySpeedupTasteGate_single_carrier_alignment_round_trip, rfl⟩

end BEDC.Derived.CauchySpeedupUp.TasteGate
