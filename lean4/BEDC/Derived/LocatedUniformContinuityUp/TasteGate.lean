import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedUniformContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedUniformContinuityUp : Type where
  | mk (X A M S D R E H C P N : BHist) : LocatedUniformContinuityUp
  deriving DecidableEq

def locatedUniformContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedUniformContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedUniformContinuityEncodeBHist h

def locatedUniformContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedUniformContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedUniformContinuityDecodeBHist tail)

private theorem LocatedUniformContinuityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedUniformContinuityDecodeBHist
        (locatedUniformContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedUniformContinuityFields : LocatedUniformContinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedUniformContinuityUp.mk X A M S D R E H C P N => [X, A, M, S, D, R, E, H, C, P, N]

def locatedUniformContinuityToEventFlow : LocatedUniformContinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedUniformContinuityFields x).map locatedUniformContinuityEncodeBHist

private def locatedUniformContinuityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedUniformContinuityEventAt index rest

def locatedUniformContinuityFromEventFlow (ef : EventFlow) :
    Option LocatedUniformContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedUniformContinuityUp.mk
      (locatedUniformContinuityDecodeBHist (locatedUniformContinuityEventAt 0 ef))
      (locatedUniformContinuityDecodeBHist (locatedUniformContinuityEventAt 1 ef))
      (locatedUniformContinuityDecodeBHist (locatedUniformContinuityEventAt 2 ef))
      (locatedUniformContinuityDecodeBHist (locatedUniformContinuityEventAt 3 ef))
      (locatedUniformContinuityDecodeBHist (locatedUniformContinuityEventAt 4 ef))
      (locatedUniformContinuityDecodeBHist (locatedUniformContinuityEventAt 5 ef))
      (locatedUniformContinuityDecodeBHist (locatedUniformContinuityEventAt 6 ef))
      (locatedUniformContinuityDecodeBHist (locatedUniformContinuityEventAt 7 ef))
      (locatedUniformContinuityDecodeBHist (locatedUniformContinuityEventAt 8 ef))
      (locatedUniformContinuityDecodeBHist (locatedUniformContinuityEventAt 9 ef))
      (locatedUniformContinuityDecodeBHist (locatedUniformContinuityEventAt 10 ef)))

private theorem LocatedUniformContinuityTasteGate_single_carrier_alignment_round_trip
    (x : LocatedUniformContinuityUp) :
    locatedUniformContinuityFromEventFlow
      (locatedUniformContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X A M S D R E H C P N =>
      change
        some
          (LocatedUniformContinuityUp.mk
            (locatedUniformContinuityDecodeBHist
              (locatedUniformContinuityEncodeBHist X))
            (locatedUniformContinuityDecodeBHist
              (locatedUniformContinuityEncodeBHist A))
            (locatedUniformContinuityDecodeBHist
              (locatedUniformContinuityEncodeBHist M))
            (locatedUniformContinuityDecodeBHist
              (locatedUniformContinuityEncodeBHist S))
            (locatedUniformContinuityDecodeBHist
              (locatedUniformContinuityEncodeBHist D))
            (locatedUniformContinuityDecodeBHist
              (locatedUniformContinuityEncodeBHist R))
            (locatedUniformContinuityDecodeBHist
              (locatedUniformContinuityEncodeBHist E))
            (locatedUniformContinuityDecodeBHist
              (locatedUniformContinuityEncodeBHist H))
            (locatedUniformContinuityDecodeBHist
              (locatedUniformContinuityEncodeBHist C))
            (locatedUniformContinuityDecodeBHist
              (locatedUniformContinuityEncodeBHist P))
            (locatedUniformContinuityDecodeBHist
              (locatedUniformContinuityEncodeBHist N))) =
          some (LocatedUniformContinuityUp.mk X A M S D R E H C P N)
      rw [LocatedUniformContinuityTasteGate_single_carrier_alignment_decode_encode X,
        LocatedUniformContinuityTasteGate_single_carrier_alignment_decode_encode A,
        LocatedUniformContinuityTasteGate_single_carrier_alignment_decode_encode M,
        LocatedUniformContinuityTasteGate_single_carrier_alignment_decode_encode S,
        LocatedUniformContinuityTasteGate_single_carrier_alignment_decode_encode D,
        LocatedUniformContinuityTasteGate_single_carrier_alignment_decode_encode R,
        LocatedUniformContinuityTasteGate_single_carrier_alignment_decode_encode E,
        LocatedUniformContinuityTasteGate_single_carrier_alignment_decode_encode H,
        LocatedUniformContinuityTasteGate_single_carrier_alignment_decode_encode C,
        LocatedUniformContinuityTasteGate_single_carrier_alignment_decode_encode P,
        LocatedUniformContinuityTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedUniformContinuityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedUniformContinuityUp} :
    locatedUniformContinuityToEventFlow x =
      locatedUniformContinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedUniformContinuityFromEventFlow (locatedUniformContinuityToEventFlow x) =
        locatedUniformContinuityFromEventFlow (locatedUniformContinuityToEventFlow y) :=
    congrArg locatedUniformContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedUniformContinuityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedUniformContinuityTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedUniformContinuityTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LocatedUniformContinuityUp,
      locatedUniformContinuityFields x = locatedUniformContinuityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ A₁ M₁ S₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ A₂ M₂ S₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance locatedUniformContinuityBHistCarrier :
    BHistCarrier LocatedUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedUniformContinuityToEventFlow
  fromEventFlow := locatedUniformContinuityFromEventFlow

instance locatedUniformContinuityChapterTasteGate :
    ChapterTasteGate LocatedUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedUniformContinuityFromEventFlow (locatedUniformContinuityToEventFlow x) =
        some x
    exact LocatedUniformContinuityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedUniformContinuityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedUniformContinuityFieldFaithful :
    FieldFaithful LocatedUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedUniformContinuityFields
  field_faithful :=
    LocatedUniformContinuityTasteGate_single_carrier_alignment_fields_faithful

instance locatedUniformContinuityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LocatedUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedUniformContinuityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      LocatedUniformContinuityUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def LocatedUniformContinuityTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate LocatedUniformContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedUniformContinuityChapterTasteGate

theorem LocatedUniformContinuityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedUniformContinuityUp) ∧
      Nonempty (FieldFaithful LocatedUniformContinuityUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial LocatedUniformContinuityUp) ∧
      (∀ h : BHist,
        locatedUniformContinuityDecodeBHist
          (locatedUniformContinuityEncodeBHist h) = h) ∧
      (∀ x : LocatedUniformContinuityUp,
        locatedUniformContinuityFromEventFlow
          (locatedUniformContinuityToEventFlow x) = some x) ∧
      (∀ x y : LocatedUniformContinuityUp,
        locatedUniformContinuityToEventFlow x =
          locatedUniformContinuityToEventFlow y → x = y) ∧
      locatedUniformContinuityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨locatedUniformContinuityChapterTasteGate⟩,
      ⟨locatedUniformContinuityFieldFaithful⟩,
      ⟨locatedUniformContinuityNontrivial⟩,
      LocatedUniformContinuityTasteGate_single_carrier_alignment_decode_encode,
      LocatedUniformContinuityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        LocatedUniformContinuityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedUniformContinuityUp
