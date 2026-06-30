import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicSelfCenterReadingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicSelfCenterReadingUp : Type where
  | packet
      (disk inscription boundary transportRow verdict replayRow provenance localName : BHist) :
      HyperbolicSelfCenterReadingUp
  deriving DecidableEq

def hyperbolicSelfCenterReadingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicSelfCenterReadingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicSelfCenterReadingEncodeBHist h

def hyperbolicSelfCenterReadingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicSelfCenterReadingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicSelfCenterReadingDecodeBHist tail)

private theorem hyperbolicSelfCenterReadingDecodeEncode :
    ∀ h : BHist,
      hyperbolicSelfCenterReadingDecodeBHist
          (hyperbolicSelfCenterReadingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperbolicSelfCenterReadingFields : HyperbolicSelfCenterReadingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicSelfCenterReadingUp.packet disk inscription boundary transportRow verdict
      replayRow provenance localName =>
      [disk, inscription, boundary, transportRow, verdict, replayRow, provenance, localName]

def hyperbolicSelfCenterReadingToEventFlow : HyperbolicSelfCenterReadingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyperbolicSelfCenterReadingFields x).map hyperbolicSelfCenterReadingEncodeBHist

private def hyperbolicSelfCenterReadingEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hyperbolicSelfCenterReadingEventAt index rest

def hyperbolicSelfCenterReadingFromEventFlow
    (ef : EventFlow) : Option HyperbolicSelfCenterReadingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperbolicSelfCenterReadingUp.packet
      (hyperbolicSelfCenterReadingDecodeBHist (hyperbolicSelfCenterReadingEventAt 0 ef))
      (hyperbolicSelfCenterReadingDecodeBHist (hyperbolicSelfCenterReadingEventAt 1 ef))
      (hyperbolicSelfCenterReadingDecodeBHist (hyperbolicSelfCenterReadingEventAt 2 ef))
      (hyperbolicSelfCenterReadingDecodeBHist (hyperbolicSelfCenterReadingEventAt 3 ef))
      (hyperbolicSelfCenterReadingDecodeBHist (hyperbolicSelfCenterReadingEventAt 4 ef))
      (hyperbolicSelfCenterReadingDecodeBHist (hyperbolicSelfCenterReadingEventAt 5 ef))
      (hyperbolicSelfCenterReadingDecodeBHist (hyperbolicSelfCenterReadingEventAt 6 ef))
      (hyperbolicSelfCenterReadingDecodeBHist (hyperbolicSelfCenterReadingEventAt 7 ef)))

private theorem hyperbolicSelfCenterReadingRoundTrip
    (x : HyperbolicSelfCenterReadingUp) :
    hyperbolicSelfCenterReadingFromEventFlow
        (hyperbolicSelfCenterReadingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | packet disk inscription boundary transportRow verdict replayRow provenance localName =>
      change
        some
          (HyperbolicSelfCenterReadingUp.packet
            (hyperbolicSelfCenterReadingDecodeBHist
              (hyperbolicSelfCenterReadingEncodeBHist disk))
            (hyperbolicSelfCenterReadingDecodeBHist
              (hyperbolicSelfCenterReadingEncodeBHist inscription))
            (hyperbolicSelfCenterReadingDecodeBHist
              (hyperbolicSelfCenterReadingEncodeBHist boundary))
            (hyperbolicSelfCenterReadingDecodeBHist
              (hyperbolicSelfCenterReadingEncodeBHist transportRow))
            (hyperbolicSelfCenterReadingDecodeBHist
              (hyperbolicSelfCenterReadingEncodeBHist verdict))
            (hyperbolicSelfCenterReadingDecodeBHist
              (hyperbolicSelfCenterReadingEncodeBHist replayRow))
            (hyperbolicSelfCenterReadingDecodeBHist
              (hyperbolicSelfCenterReadingEncodeBHist provenance))
            (hyperbolicSelfCenterReadingDecodeBHist
              (hyperbolicSelfCenterReadingEncodeBHist localName))) =
          some
            (HyperbolicSelfCenterReadingUp.packet disk inscription boundary transportRow
              verdict replayRow provenance localName)
      rw [hyperbolicSelfCenterReadingDecodeEncode disk,
        hyperbolicSelfCenterReadingDecodeEncode inscription,
        hyperbolicSelfCenterReadingDecodeEncode boundary,
        hyperbolicSelfCenterReadingDecodeEncode transportRow,
        hyperbolicSelfCenterReadingDecodeEncode verdict,
        hyperbolicSelfCenterReadingDecodeEncode replayRow,
        hyperbolicSelfCenterReadingDecodeEncode provenance,
        hyperbolicSelfCenterReadingDecodeEncode localName]

private theorem hyperbolicSelfCenterReadingToEventFlow_injective
    {x y : HyperbolicSelfCenterReadingUp} :
    hyperbolicSelfCenterReadingToEventFlow x =
        hyperbolicSelfCenterReadingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicSelfCenterReadingFromEventFlow
          (hyperbolicSelfCenterReadingToEventFlow x) =
        hyperbolicSelfCenterReadingFromEventFlow
          (hyperbolicSelfCenterReadingToEventFlow y) :=
    congrArg hyperbolicSelfCenterReadingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hyperbolicSelfCenterReadingRoundTrip x).symm
      (Eq.trans hread (hyperbolicSelfCenterReadingRoundTrip y)))

private theorem hyperbolicSelfCenterReadingFields_faithful :
    ∀ x y : HyperbolicSelfCenterReadingUp,
      hyperbolicSelfCenterReadingFields x = hyperbolicSelfCenterReadingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | packet disk₁ inscription₁ boundary₁ transport₁ verdict₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | packet disk₂ inscription₂ boundary₂ transport₂ verdict₂ replay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance hyperbolicSelfCenterReadingBHistCarrier :
    BHistCarrier HyperbolicSelfCenterReadingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicSelfCenterReadingToEventFlow
  fromEventFlow := hyperbolicSelfCenterReadingFromEventFlow

instance hyperbolicSelfCenterReadingChapterTasteGate :
    ChapterTasteGate HyperbolicSelfCenterReadingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicSelfCenterReadingFromEventFlow
          (hyperbolicSelfCenterReadingToEventFlow x) = some x
    exact hyperbolicSelfCenterReadingRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hyperbolicSelfCenterReadingToEventFlow_injective heq)

instance hyperbolicSelfCenterReadingFieldFaithful :
    FieldFaithful HyperbolicSelfCenterReadingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicSelfCenterReadingFields
  field_faithful := hyperbolicSelfCenterReadingFields_faithful

instance hyperbolicSelfCenterReadingNontrivial :
    Nontrivial HyperbolicSelfCenterReadingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicSelfCenterReadingUp.packet (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HyperbolicSelfCenterReadingUp.packet (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HyperbolicSelfCenterReadingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyperbolicSelfCenterReadingChapterTasteGate

theorem HyperbolicSelfCenterReadingTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier HyperbolicSelfCenterReadingUp) ∧
      Nonempty (ChapterTasteGate HyperbolicSelfCenterReadingUp) ∧
      Nonempty (FieldFaithful HyperbolicSelfCenterReadingUp) ∧
      Nonempty (Nontrivial HyperbolicSelfCenterReadingUp) ∧
      (∀ h : BHist,
        hyperbolicSelfCenterReadingDecodeBHist
            (hyperbolicSelfCenterReadingEncodeBHist h) = h) ∧
      (∀ x : HyperbolicSelfCenterReadingUp,
        hyperbolicSelfCenterReadingFromEventFlow
            (hyperbolicSelfCenterReadingToEventFlow x) = some x) ∧
      (∀ x y : HyperbolicSelfCenterReadingUp,
        hyperbolicSelfCenterReadingToEventFlow x =
          hyperbolicSelfCenterReadingToEventFlow y → x = y) ∧
      hyperbolicSelfCenterReadingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨hyperbolicSelfCenterReadingBHistCarrier⟩
  constructor
  · exact ⟨hyperbolicSelfCenterReadingChapterTasteGate⟩
  constructor
  · exact ⟨hyperbolicSelfCenterReadingFieldFaithful⟩
  constructor
  · exact ⟨hyperbolicSelfCenterReadingNontrivial⟩
  constructor
  · exact hyperbolicSelfCenterReadingDecodeEncode
  constructor
  · exact hyperbolicSelfCenterReadingRoundTrip
  constructor
  · intro x y heq
    exact hyperbolicSelfCenterReadingToEventFlow_injective heq
  · rfl

end BEDC.Derived.HyperbolicSelfCenterReadingUp
