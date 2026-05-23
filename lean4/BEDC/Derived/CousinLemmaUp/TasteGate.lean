import BEDC.Derived.CousinLemmaUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CousinLemmaUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def cousinLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cousinLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cousinLemmaEncodeBHist h

def cousinLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cousinLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cousinLemmaDecodeBHist tail)

private theorem CousinLemmaTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cousinLemmaDecodeBHist (cousinLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cousinLemmaFields : BEDC.Derived.CousinLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CousinLemmaUp.mk I G T M W R E H C P N => [I, G, T, M, W, R, E, H, C, P, N]

def cousinLemmaToEventFlow : BEDC.Derived.CousinLemmaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cousinLemmaFields x).map cousinLemmaEncodeBHist

private def cousinLemmaEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cousinLemmaEventAt index rest

def cousinLemmaFromEventFlow (ef : EventFlow) : Option BEDC.Derived.CousinLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CousinLemmaUp.mk
      (cousinLemmaDecodeBHist (cousinLemmaEventAt 0 ef))
      (cousinLemmaDecodeBHist (cousinLemmaEventAt 1 ef))
      (cousinLemmaDecodeBHist (cousinLemmaEventAt 2 ef))
      (cousinLemmaDecodeBHist (cousinLemmaEventAt 3 ef))
      (cousinLemmaDecodeBHist (cousinLemmaEventAt 4 ef))
      (cousinLemmaDecodeBHist (cousinLemmaEventAt 5 ef))
      (cousinLemmaDecodeBHist (cousinLemmaEventAt 6 ef))
      (cousinLemmaDecodeBHist (cousinLemmaEventAt 7 ef))
      (cousinLemmaDecodeBHist (cousinLemmaEventAt 8 ef))
      (cousinLemmaDecodeBHist (cousinLemmaEventAt 9 ef))
      (cousinLemmaDecodeBHist (cousinLemmaEventAt 10 ef)))

private theorem CousinLemmaTasteGate_single_carrier_alignment_round_trip
    (x : BEDC.Derived.CousinLemmaUp) :
    cousinLemmaFromEventFlow (cousinLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I G T M W R E H C P N =>
      change
        some
          (CousinLemmaUp.mk
            (cousinLemmaDecodeBHist (cousinLemmaEncodeBHist I))
            (cousinLemmaDecodeBHist (cousinLemmaEncodeBHist G))
            (cousinLemmaDecodeBHist (cousinLemmaEncodeBHist T))
            (cousinLemmaDecodeBHist (cousinLemmaEncodeBHist M))
            (cousinLemmaDecodeBHist (cousinLemmaEncodeBHist W))
            (cousinLemmaDecodeBHist (cousinLemmaEncodeBHist R))
            (cousinLemmaDecodeBHist (cousinLemmaEncodeBHist E))
            (cousinLemmaDecodeBHist (cousinLemmaEncodeBHist H))
            (cousinLemmaDecodeBHist (cousinLemmaEncodeBHist C))
            (cousinLemmaDecodeBHist (cousinLemmaEncodeBHist P))
            (cousinLemmaDecodeBHist (cousinLemmaEncodeBHist N))) =
          some (CousinLemmaUp.mk I G T M W R E H C P N)
      rw [CousinLemmaTasteGate_single_carrier_alignment_decode_encode I,
        CousinLemmaTasteGate_single_carrier_alignment_decode_encode G,
        CousinLemmaTasteGate_single_carrier_alignment_decode_encode T,
        CousinLemmaTasteGate_single_carrier_alignment_decode_encode M,
        CousinLemmaTasteGate_single_carrier_alignment_decode_encode W,
        CousinLemmaTasteGate_single_carrier_alignment_decode_encode R,
        CousinLemmaTasteGate_single_carrier_alignment_decode_encode E,
        CousinLemmaTasteGate_single_carrier_alignment_decode_encode H,
        CousinLemmaTasteGate_single_carrier_alignment_decode_encode C,
        CousinLemmaTasteGate_single_carrier_alignment_decode_encode P,
        CousinLemmaTasteGate_single_carrier_alignment_decode_encode N]

private theorem CousinLemmaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BEDC.Derived.CousinLemmaUp} :
    cousinLemmaToEventFlow x = cousinLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cousinLemmaFromEventFlow (cousinLemmaToEventFlow x) =
        cousinLemmaFromEventFlow (cousinLemmaToEventFlow y) :=
    congrArg cousinLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CousinLemmaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CousinLemmaTasteGate_single_carrier_alignment_round_trip y)))

private theorem CousinLemmaTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BEDC.Derived.CousinLemmaUp,
      cousinLemmaFields x = cousinLemmaFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ G₁ T₁ M₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ G₂ T₂ M₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cousinLemmaBHistCarrier : BHistCarrier BEDC.Derived.CousinLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cousinLemmaToEventFlow
  fromEventFlow := cousinLemmaFromEventFlow

instance cousinLemmaChapterTasteGate : ChapterTasteGate BEDC.Derived.CousinLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cousinLemmaFromEventFlow (cousinLemmaToEventFlow x) = some x
    exact CousinLemmaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CousinLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cousinLemmaFieldFaithful : FieldFaithful BEDC.Derived.CousinLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cousinLemmaFields
  field_faithful := CousinLemmaTasteGate_single_carrier_alignment_fields_faithful

instance cousinLemmaNontrivial : Nontrivial BEDC.Derived.CousinLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CousinLemmaUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CousinLemmaUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CousinLemmaTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BEDC.Derived.CousinLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cousinLemmaChapterTasteGate

theorem CousinLemmaTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BEDC.Derived.CousinLemmaUp) ∧
      (∀ h : BHist, cousinLemmaDecodeBHist (cousinLemmaEncodeBHist h) = h) ∧
        (∀ x : BEDC.Derived.CousinLemmaUp,
          cousinLemmaFromEventFlow (cousinLemmaToEventFlow x) = some x) ∧
          cousinLemmaEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨cousinLemmaChapterTasteGate⟩,
      CousinLemmaTasteGate_single_carrier_alignment_decode_encode,
      CousinLemmaTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.CousinLemmaUp.TasteGate
