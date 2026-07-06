import BEDC.Derived.ClosurePreservationAuditWitnessUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosurePreservationAuditWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosurePreservationAuditWitnessUp : Type where
  | mk (S V F B R H C P N : BHist) : ClosurePreservationAuditWitnessUp

def ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_encode_bhist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 ::
        ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_encode_bhist h
  | BHist.e1 h =>
      BMark.b1 ::
        ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_encode_bhist h

def ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist tail)

private theorem ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
          (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_encode_bhist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_fields :
    ClosurePreservationAuditWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosurePreservationAuditWitnessUp.mk S V F B R H C P N =>
      [S, V, F, B, R, H, C, P, N]

def ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_toEventFlow :
    ClosurePreservationAuditWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_fields x).map
        ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_encode_bhist

private def ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_eventAt index rest

def ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option ClosurePreservationAuditWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosurePreservationAuditWitnessUp.mk
      (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
        (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_eventAt 0 ef))
      (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
        (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_eventAt 1 ef))
      (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
        (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_eventAt 2 ef))
      (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
        (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_eventAt 3 ef))
      (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
        (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_eventAt 4 ef))
      (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
        (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_eventAt 5 ef))
      (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
        (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_eventAt 6 ef))
      (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
        (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_eventAt 7 ef))
      (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
        (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ClosurePreservationAuditWitnessUp,
      ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_fromEventFlow
          (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S V F B R H C P N =>
      change
        some
            (ClosurePreservationAuditWitnessUp.mk
              (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
                (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_encode_bhist S))
              (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
                (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_encode_bhist V))
              (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
                (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_encode_bhist F))
              (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
                (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_encode_bhist B))
              (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
                (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_encode_bhist R))
              (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
                (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_encode_bhist H))
              (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
                (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_encode_bhist C))
              (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
                (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_encode_bhist P))
              (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_bhist
                (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_encode_bhist N))) =
          some (ClosurePreservationAuditWitnessUp.mk S V F B R H C P N)
      rw [ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_encode S,
        ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_encode V,
        ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_encode F,
        ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_encode B,
        ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_encode R,
        ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_encode H,
        ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_encode C,
        ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_encode P,
        ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_decode_encode N]

private theorem ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_injective
    {x y : ClosurePreservationAuditWitnessUp} :
    ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_toEventFlow x =
        ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_fromEventFlow
          (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_toEventFlow x) =
        ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_fromEventFlow
          (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_round_trip y)))

instance closurePreservationAuditWitnessBHistCarrier :
    BHistCarrier ClosurePreservationAuditWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_fromEventFlow

instance closurePreservationAuditWitnessChapterTasteGate :
    ChapterTasteGate ClosurePreservationAuditWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_fromEventFlow
          (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment_injective heq)

namespace TasteGate

theorem ClosurePreservationAuditWitnessTasteGate_single_carrier_alignment :
    Nonempty (BEDC.Meta.TasteGate.BHistCarrier ClosurePreservationAuditWitnessUp) ∧
      Nonempty (BEDC.Meta.TasteGate.ChapterTasteGate ClosurePreservationAuditWitnessUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨closurePreservationAuditWitnessBHistCarrier⟩,
      ⟨closurePreservationAuditWitnessChapterTasteGate⟩⟩

end TasteGate

end BEDC.Derived.ClosurePreservationAuditWitnessUp
