import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CousinFiniteCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CousinFiniteCoverUp : Type where
  | mk (I G C T M W R E H P N : BHist) : CousinFiniteCoverUp
  deriving DecidableEq

def cousinFiniteCoverEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cousinFiniteCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cousinFiniteCoverEncodeBHist h

def cousinFiniteCoverDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cousinFiniteCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cousinFiniteCoverDecodeBHist tail)

private theorem CousinFiniteCoverTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cousinFiniteCoverDecodeBHist (cousinFiniteCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cousinFiniteCoverFields : CousinFiniteCoverUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CousinFiniteCoverUp.mk I G C T M W R E H P N => [I, G, C, T, M, W, R, E, H, P, N]

def cousinFiniteCoverToEventFlow : CousinFiniteCoverUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cousinFiniteCoverFields x).map cousinFiniteCoverEncodeBHist

private def cousinFiniteCoverEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cousinFiniteCoverEventAt index rest

def cousinFiniteCoverFromEventFlow (ef : EventFlow) : Option CousinFiniteCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CousinFiniteCoverUp.mk
      (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEventAt 0 ef))
      (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEventAt 1 ef))
      (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEventAt 2 ef))
      (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEventAt 3 ef))
      (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEventAt 4 ef))
      (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEventAt 5 ef))
      (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEventAt 6 ef))
      (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEventAt 7 ef))
      (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEventAt 8 ef))
      (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEventAt 9 ef))
      (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEventAt 10 ef)))

private theorem CousinFiniteCoverTasteGate_single_carrier_alignment_round_trip
    (x : CousinFiniteCoverUp) :
    cousinFiniteCoverFromEventFlow (cousinFiniteCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I G C T M W R E H P N =>
      change
        some
          (CousinFiniteCoverUp.mk
            (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEncodeBHist I))
            (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEncodeBHist G))
            (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEncodeBHist C))
            (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEncodeBHist T))
            (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEncodeBHist M))
            (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEncodeBHist W))
            (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEncodeBHist R))
            (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEncodeBHist E))
            (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEncodeBHist H))
            (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEncodeBHist P))
            (cousinFiniteCoverDecodeBHist (cousinFiniteCoverEncodeBHist N))) =
          some (CousinFiniteCoverUp.mk I G C T M W R E H P N)
      rw [CousinFiniteCoverTasteGate_single_carrier_alignment_decode_encode I,
        CousinFiniteCoverTasteGate_single_carrier_alignment_decode_encode G,
        CousinFiniteCoverTasteGate_single_carrier_alignment_decode_encode C,
        CousinFiniteCoverTasteGate_single_carrier_alignment_decode_encode T,
        CousinFiniteCoverTasteGate_single_carrier_alignment_decode_encode M,
        CousinFiniteCoverTasteGate_single_carrier_alignment_decode_encode W,
        CousinFiniteCoverTasteGate_single_carrier_alignment_decode_encode R,
        CousinFiniteCoverTasteGate_single_carrier_alignment_decode_encode E,
        CousinFiniteCoverTasteGate_single_carrier_alignment_decode_encode H,
        CousinFiniteCoverTasteGate_single_carrier_alignment_decode_encode P,
        CousinFiniteCoverTasteGate_single_carrier_alignment_decode_encode N]

private theorem CousinFiniteCoverTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CousinFiniteCoverUp} :
    cousinFiniteCoverToEventFlow x = cousinFiniteCoverToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cousinFiniteCoverFromEventFlow (cousinFiniteCoverToEventFlow x) =
        cousinFiniteCoverFromEventFlow (cousinFiniteCoverToEventFlow y) :=
    congrArg cousinFiniteCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CousinFiniteCoverTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CousinFiniteCoverTasteGate_single_carrier_alignment_round_trip y)))

private theorem CousinFiniteCoverTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CousinFiniteCoverUp, cousinFiniteCoverFields x = cousinFiniteCoverFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ G₁ C₁ T₁ M₁ W₁ R₁ E₁ H₁ P₁ N₁ =>
      cases y with
      | mk I₂ G₂ C₂ T₂ M₂ W₂ R₂ E₂ H₂ P₂ N₂ =>
          cases hfields
          rfl

instance cousinFiniteCoverBHistCarrier : BHistCarrier CousinFiniteCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cousinFiniteCoverToEventFlow
  fromEventFlow := cousinFiniteCoverFromEventFlow

instance cousinFiniteCoverChapterTasteGate : ChapterTasteGate CousinFiniteCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cousinFiniteCoverFromEventFlow (cousinFiniteCoverToEventFlow x) = some x
    exact CousinFiniteCoverTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CousinFiniteCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cousinFiniteCoverFieldFaithful : FieldFaithful CousinFiniteCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cousinFiniteCoverFields
  field_faithful := CousinFiniteCoverTasteGate_single_carrier_alignment_fields_faithful

instance cousinFiniteCoverNontrivial : Nontrivial CousinFiniteCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CousinFiniteCoverUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CousinFiniteCoverUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CousinFiniteCoverTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CousinFiniteCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cousinFiniteCoverChapterTasteGate

theorem CousinFiniteCoverTasteGate_single_carrier_alignment :
    (∀ h : BHist, cousinFiniteCoverDecodeBHist (cousinFiniteCoverEncodeBHist h) = h) ∧
      (∀ x : CousinFiniteCoverUp,
        cousinFiniteCoverFromEventFlow (cousinFiniteCoverToEventFlow x) = some x) ∧
        (∀ x y : CousinFiniteCoverUp,
          cousinFiniteCoverToEventFlow x = cousinFiniteCoverToEventFlow y -> x = y) ∧
          cousinFiniteCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨CousinFiniteCoverTasteGate_single_carrier_alignment_decode_encode,
      CousinFiniteCoverTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CousinFiniteCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CousinFiniteCoverUp
