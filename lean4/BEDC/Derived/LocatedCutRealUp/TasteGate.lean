import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCutRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCutRealUp : Type where
  | mk (D G W R Q E H C P N : BHist) : LocatedCutRealUp
  deriving DecidableEq

def locatedCutRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCutRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCutRealEncodeBHist h

def locatedCutRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCutRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCutRealDecodeBHist tail)

private theorem LocatedCutRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, locatedCutRealDecodeBHist (locatedCutRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCutRealFields : LocatedCutRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCutRealUp.mk D G W R Q E H C P N => [D, G, W, R, Q, E, H, C, P, N]

def locatedCutRealToEventFlow : LocatedCutRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCutRealUp.mk D G W R Q E H C P N =>
      (locatedCutRealFields (LocatedCutRealUp.mk D G W R Q E H C P N)).map
        locatedCutRealEncodeBHist

private def locatedCutRealEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedCutRealEventAt index rest

def locatedCutRealFromEventFlow (ef : EventFlow) : Option LocatedCutRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCutRealUp.mk
      (locatedCutRealDecodeBHist (locatedCutRealEventAt 0 ef))
      (locatedCutRealDecodeBHist (locatedCutRealEventAt 1 ef))
      (locatedCutRealDecodeBHist (locatedCutRealEventAt 2 ef))
      (locatedCutRealDecodeBHist (locatedCutRealEventAt 3 ef))
      (locatedCutRealDecodeBHist (locatedCutRealEventAt 4 ef))
      (locatedCutRealDecodeBHist (locatedCutRealEventAt 5 ef))
      (locatedCutRealDecodeBHist (locatedCutRealEventAt 6 ef))
      (locatedCutRealDecodeBHist (locatedCutRealEventAt 7 ef))
      (locatedCutRealDecodeBHist (locatedCutRealEventAt 8 ef))
      (locatedCutRealDecodeBHist (locatedCutRealEventAt 9 ef)))

private theorem LocatedCutRealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedCutRealUp,
      locatedCutRealFromEventFlow (locatedCutRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D G W R Q E H C P N =>
      change
        some
          (LocatedCutRealUp.mk
            (locatedCutRealDecodeBHist (locatedCutRealEncodeBHist D))
            (locatedCutRealDecodeBHist (locatedCutRealEncodeBHist G))
            (locatedCutRealDecodeBHist (locatedCutRealEncodeBHist W))
            (locatedCutRealDecodeBHist (locatedCutRealEncodeBHist R))
            (locatedCutRealDecodeBHist (locatedCutRealEncodeBHist Q))
            (locatedCutRealDecodeBHist (locatedCutRealEncodeBHist E))
            (locatedCutRealDecodeBHist (locatedCutRealEncodeBHist H))
            (locatedCutRealDecodeBHist (locatedCutRealEncodeBHist C))
            (locatedCutRealDecodeBHist (locatedCutRealEncodeBHist P))
            (locatedCutRealDecodeBHist (locatedCutRealEncodeBHist N))) =
          some (LocatedCutRealUp.mk D G W R Q E H C P N)
      rw [LocatedCutRealTasteGate_single_carrier_alignment_decode_encode D,
        LocatedCutRealTasteGate_single_carrier_alignment_decode_encode G,
        LocatedCutRealTasteGate_single_carrier_alignment_decode_encode W,
        LocatedCutRealTasteGate_single_carrier_alignment_decode_encode R,
        LocatedCutRealTasteGate_single_carrier_alignment_decode_encode Q,
        LocatedCutRealTasteGate_single_carrier_alignment_decode_encode E,
        LocatedCutRealTasteGate_single_carrier_alignment_decode_encode H,
        LocatedCutRealTasteGate_single_carrier_alignment_decode_encode C,
        LocatedCutRealTasteGate_single_carrier_alignment_decode_encode P,
        LocatedCutRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedCutRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedCutRealUp} :
    locatedCutRealToEventFlow x = locatedCutRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCutRealFromEventFlow (locatedCutRealToEventFlow x) =
        locatedCutRealFromEventFlow (locatedCutRealToEventFlow y) :=
    congrArg locatedCutRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedCutRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedCutRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedCutRealTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LocatedCutRealUp, locatedCutRealFields x = locatedCutRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ G₁ W₁ R₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ G₂ W₂ R₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance locatedCutRealBHistCarrier : BHistCarrier LocatedCutRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCutRealToEventFlow
  fromEventFlow := locatedCutRealFromEventFlow

instance locatedCutRealChapterTasteGate : ChapterTasteGate LocatedCutRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCutRealFromEventFlow (locatedCutRealToEventFlow x) = some x
    exact LocatedCutRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedCutRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedCutRealFieldFaithful : FieldFaithful LocatedCutRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedCutRealFields
  field_faithful := LocatedCutRealTasteGate_single_carrier_alignment_fields_faithful

instance locatedCutRealNontrivial : Nontrivial LocatedCutRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedCutRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedCutRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedCutRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCutRealChapterTasteGate

theorem LocatedCutRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedCutRealDecodeBHist (locatedCutRealEncodeBHist h) = h) ∧
      (∀ x : LocatedCutRealUp,
        locatedCutRealFromEventFlow (locatedCutRealToEventFlow x) = some x) ∧
        (∀ x y : LocatedCutRealUp,
          locatedCutRealToEventFlow x = locatedCutRealToEventFlow y → x = y) ∧
          locatedCutRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨LocatedCutRealTasteGate_single_carrier_alignment_decode_encode,
      LocatedCutRealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => LocatedCutRealTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedCutRealUp
