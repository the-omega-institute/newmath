import BEDC.Derived.RootChoiceSeparationUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RootChoiceSeparationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def rootChoiceSeparationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rootChoiceSeparationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rootChoiceSeparationEncodeBHist h

def rootChoiceSeparationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rootChoiceSeparationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rootChoiceSeparationDecodeBHist tail)

private theorem RootChoiceSeparationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      rootChoiceSeparationDecodeBHist (rootChoiceSeparationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rootChoiceSeparationFields : BEDC.Derived.RootChoiceSeparationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.RootChoiceSeparationUp.mk functionRead interval apartness bisectionSchedule
      stream regSeq realSeal transport replay provenance name =>
      [functionRead, interval, apartness, bisectionSchedule, stream, regSeq, realSeal,
        transport, replay, provenance, name]

def rootChoiceSeparationToEventFlow : BEDC.Derived.RootChoiceSeparationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rootChoiceSeparationFields x).map rootChoiceSeparationEncodeBHist

private def rootChoiceSeparationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rootChoiceSeparationEventAt index rest

def rootChoiceSeparationFromEventFlow
    (ef : EventFlow) : Option BEDC.Derived.RootChoiceSeparationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BEDC.Derived.RootChoiceSeparationUp.mk
      (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEventAt 0 ef))
      (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEventAt 1 ef))
      (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEventAt 2 ef))
      (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEventAt 3 ef))
      (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEventAt 4 ef))
      (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEventAt 5 ef))
      (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEventAt 6 ef))
      (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEventAt 7 ef))
      (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEventAt 8 ef))
      (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEventAt 9 ef))
      (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEventAt 10 ef)))

private theorem RootChoiceSeparationTasteGate_single_carrier_alignment_round_trip
    (x : BEDC.Derived.RootChoiceSeparationUp) :
    rootChoiceSeparationFromEventFlow (rootChoiceSeparationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk functionRead interval apartness bisectionSchedule stream regSeq realSeal transport replay
      provenance name =>
      change
        some
          (BEDC.Derived.RootChoiceSeparationUp.mk
            (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEncodeBHist functionRead))
            (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEncodeBHist interval))
            (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEncodeBHist apartness))
            (rootChoiceSeparationDecodeBHist
              (rootChoiceSeparationEncodeBHist bisectionSchedule))
            (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEncodeBHist stream))
            (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEncodeBHist regSeq))
            (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEncodeBHist realSeal))
            (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEncodeBHist transport))
            (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEncodeBHist replay))
            (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEncodeBHist provenance))
            (rootChoiceSeparationDecodeBHist (rootChoiceSeparationEncodeBHist name))) =
          some
            (BEDC.Derived.RootChoiceSeparationUp.mk functionRead interval apartness
              bisectionSchedule stream regSeq realSeal transport replay provenance name)
      rw [RootChoiceSeparationTasteGate_single_carrier_alignment_decode_encode functionRead,
        RootChoiceSeparationTasteGate_single_carrier_alignment_decode_encode interval,
        RootChoiceSeparationTasteGate_single_carrier_alignment_decode_encode apartness,
        RootChoiceSeparationTasteGate_single_carrier_alignment_decode_encode
          bisectionSchedule,
        RootChoiceSeparationTasteGate_single_carrier_alignment_decode_encode stream,
        RootChoiceSeparationTasteGate_single_carrier_alignment_decode_encode regSeq,
        RootChoiceSeparationTasteGate_single_carrier_alignment_decode_encode realSeal,
        RootChoiceSeparationTasteGate_single_carrier_alignment_decode_encode transport,
        RootChoiceSeparationTasteGate_single_carrier_alignment_decode_encode replay,
        RootChoiceSeparationTasteGate_single_carrier_alignment_decode_encode provenance,
        RootChoiceSeparationTasteGate_single_carrier_alignment_decode_encode name]

private theorem RootChoiceSeparationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BEDC.Derived.RootChoiceSeparationUp} :
    rootChoiceSeparationToEventFlow x = rootChoiceSeparationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rootChoiceSeparationFromEventFlow (rootChoiceSeparationToEventFlow x) =
        rootChoiceSeparationFromEventFlow (rootChoiceSeparationToEventFlow y) :=
    congrArg rootChoiceSeparationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RootChoiceSeparationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RootChoiceSeparationTasteGate_single_carrier_alignment_round_trip y)))

private theorem RootChoiceSeparationTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BEDC.Derived.RootChoiceSeparationUp,
      rootChoiceSeparationFields x = rootChoiceSeparationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk functionRead₁ interval₁ apartness₁ bisectionSchedule₁ stream₁ regSeq₁ realSeal₁
      transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk functionRead₂ interval₂ apartness₂ bisectionSchedule₂ stream₂ regSeq₂ realSeal₂
          transport₂ replay₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance rootChoiceSeparationBHistCarrier :
    BHistCarrier BEDC.Derived.RootChoiceSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rootChoiceSeparationToEventFlow
  fromEventFlow := rootChoiceSeparationFromEventFlow

instance rootChoiceSeparationChapterTasteGate :
    ChapterTasteGate BEDC.Derived.RootChoiceSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rootChoiceSeparationFromEventFlow (rootChoiceSeparationToEventFlow x) = some x
    exact RootChoiceSeparationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RootChoiceSeparationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance rootChoiceSeparationFieldFaithful :
    FieldFaithful BEDC.Derived.RootChoiceSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rootChoiceSeparationFields
  field_faithful := RootChoiceSeparationTasteGate_single_carrier_alignment_fields_faithful

instance rootChoiceSeparationNontrivial :
    Nontrivial BEDC.Derived.RootChoiceSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BEDC.Derived.RootChoiceSeparationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      BEDC.Derived.RootChoiceSeparationUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def RootChoiceSeparationTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BEDC.Derived.RootChoiceSeparationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rootChoiceSeparationChapterTasteGate

theorem RootChoiceSeparationTasteGate_single_carrier_alignment :
    (∀ h : BHist, rootChoiceSeparationDecodeBHist (rootChoiceSeparationEncodeBHist h) = h) ∧
      (∀ x : BEDC.Derived.RootChoiceSeparationUp,
        rootChoiceSeparationFromEventFlow (rootChoiceSeparationToEventFlow x) = some x) ∧
        (∀ x y : BEDC.Derived.RootChoiceSeparationUp,
          rootChoiceSeparationToEventFlow x = rootChoiceSeparationToEventFlow y → x = y) ∧
          rootChoiceSeparationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RootChoiceSeparationTasteGate_single_carrier_alignment_decode_encode,
      RootChoiceSeparationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RootChoiceSeparationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RootChoiceSeparationUp
