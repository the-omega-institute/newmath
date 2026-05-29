import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MedianLeakageSpectrumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MedianLeakageSpectrumUp : Type where
  | mk (W T A M I G D H C P N : BHist) : MedianLeakageSpectrumUp
  deriving DecidableEq

def MedianLeakageSpectrumUp_single_carrier_alignment_encodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: MedianLeakageSpectrumUp_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: MedianLeakageSpectrumUp_single_carrier_alignment_encodeBHist h

def MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist tail)

private theorem MedianLeakageSpectrumUp_single_carrier_alignment_decode_encode :
    forall h : BHist, MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist
      (MedianLeakageSpectrumUp_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def MedianLeakageSpectrumUp_single_carrier_alignment_fields : MedianLeakageSpectrumUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MedianLeakageSpectrumUp.mk W T A M I G D H C P N =>
      [W, T, A, M, I, G, D, H, C, P, N]

def MedianLeakageSpectrumUp_single_carrier_alignment_toEventFlow : MedianLeakageSpectrumUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (MedianLeakageSpectrumUp_single_carrier_alignment_fields x).map
        MedianLeakageSpectrumUp_single_carrier_alignment_encodeBHist

private def MedianLeakageSpectrumUp_single_carrier_alignment_eventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => MedianLeakageSpectrumUp_single_carrier_alignment_eventAt index rest

def MedianLeakageSpectrumUp_single_carrier_alignment_fromEventFlow (ef : EventFlow) : Option MedianLeakageSpectrumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MedianLeakageSpectrumUp.mk
      (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist
        (MedianLeakageSpectrumUp_single_carrier_alignment_eventAt 0 ef))
      (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist
        (MedianLeakageSpectrumUp_single_carrier_alignment_eventAt 1 ef))
      (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist
        (MedianLeakageSpectrumUp_single_carrier_alignment_eventAt 2 ef))
      (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist
        (MedianLeakageSpectrumUp_single_carrier_alignment_eventAt 3 ef))
      (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist
        (MedianLeakageSpectrumUp_single_carrier_alignment_eventAt 4 ef))
      (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist
        (MedianLeakageSpectrumUp_single_carrier_alignment_eventAt 5 ef))
      (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist
        (MedianLeakageSpectrumUp_single_carrier_alignment_eventAt 6 ef))
      (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist
        (MedianLeakageSpectrumUp_single_carrier_alignment_eventAt 7 ef))
      (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist
        (MedianLeakageSpectrumUp_single_carrier_alignment_eventAt 8 ef))
      (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist
        (MedianLeakageSpectrumUp_single_carrier_alignment_eventAt 9 ef))
      (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist
        (MedianLeakageSpectrumUp_single_carrier_alignment_eventAt 10 ef)))

private theorem MedianLeakageSpectrumUp_single_carrier_alignment_round_trip
    (x : MedianLeakageSpectrumUp) :
    MedianLeakageSpectrumUp_single_carrier_alignment_fromEventFlow
      (MedianLeakageSpectrumUp_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk W T A M I G D H C P N =>
      change
        some
          (MedianLeakageSpectrumUp.mk
            (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist (MedianLeakageSpectrumUp_single_carrier_alignment_encodeBHist W))
            (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist (MedianLeakageSpectrumUp_single_carrier_alignment_encodeBHist T))
            (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist (MedianLeakageSpectrumUp_single_carrier_alignment_encodeBHist A))
            (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist (MedianLeakageSpectrumUp_single_carrier_alignment_encodeBHist M))
            (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist (MedianLeakageSpectrumUp_single_carrier_alignment_encodeBHist I))
            (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist (MedianLeakageSpectrumUp_single_carrier_alignment_encodeBHist G))
            (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist (MedianLeakageSpectrumUp_single_carrier_alignment_encodeBHist D))
            (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist (MedianLeakageSpectrumUp_single_carrier_alignment_encodeBHist H))
            (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist (MedianLeakageSpectrumUp_single_carrier_alignment_encodeBHist C))
            (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist (MedianLeakageSpectrumUp_single_carrier_alignment_encodeBHist P))
            (MedianLeakageSpectrumUp_single_carrier_alignment_decodeBHist (MedianLeakageSpectrumUp_single_carrier_alignment_encodeBHist N))) =
          some (MedianLeakageSpectrumUp.mk W T A M I G D H C P N)
      rw [MedianLeakageSpectrumUp_single_carrier_alignment_decode_encode W,
        MedianLeakageSpectrumUp_single_carrier_alignment_decode_encode T,
        MedianLeakageSpectrumUp_single_carrier_alignment_decode_encode A,
        MedianLeakageSpectrumUp_single_carrier_alignment_decode_encode M,
        MedianLeakageSpectrumUp_single_carrier_alignment_decode_encode I,
        MedianLeakageSpectrumUp_single_carrier_alignment_decode_encode G,
        MedianLeakageSpectrumUp_single_carrier_alignment_decode_encode D,
        MedianLeakageSpectrumUp_single_carrier_alignment_decode_encode H,
        MedianLeakageSpectrumUp_single_carrier_alignment_decode_encode C,
        MedianLeakageSpectrumUp_single_carrier_alignment_decode_encode P,
        MedianLeakageSpectrumUp_single_carrier_alignment_decode_encode N]

private theorem MedianLeakageSpectrumUp_single_carrier_alignment_toEventFlow_injective
    {x y : MedianLeakageSpectrumUp} :
    MedianLeakageSpectrumUp_single_carrier_alignment_toEventFlow x = MedianLeakageSpectrumUp_single_carrier_alignment_toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      MedianLeakageSpectrumUp_single_carrier_alignment_fromEventFlow (MedianLeakageSpectrumUp_single_carrier_alignment_toEventFlow x) =
        MedianLeakageSpectrumUp_single_carrier_alignment_fromEventFlow (MedianLeakageSpectrumUp_single_carrier_alignment_toEventFlow y) :=
    congrArg MedianLeakageSpectrumUp_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MedianLeakageSpectrumUp_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MedianLeakageSpectrumUp_single_carrier_alignment_round_trip y)))

private theorem MedianLeakageSpectrumUp_single_carrier_alignment_fields_injective :
    forall x y : MedianLeakageSpectrumUp,
      MedianLeakageSpectrumUp_single_carrier_alignment_fields x = MedianLeakageSpectrumUp_single_carrier_alignment_fields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W1 T1 A1 M1 I1 G1 D1 H1 C1 P1 N1 =>
      cases y with
      | mk W2 T2 A2 M2 I2 G2 D2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance MedianLeakageSpectrumUp_single_carrier_alignment_bhist_carrier : BHistCarrier MedianLeakageSpectrumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := MedianLeakageSpectrumUp_single_carrier_alignment_toEventFlow
  fromEventFlow := MedianLeakageSpectrumUp_single_carrier_alignment_fromEventFlow

instance MedianLeakageSpectrumUp_single_carrier_alignment_chapter_taste_gate :
    ChapterTasteGate MedianLeakageSpectrumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change MedianLeakageSpectrumUp_single_carrier_alignment_fromEventFlow (MedianLeakageSpectrumUp_single_carrier_alignment_toEventFlow x) = some x
    exact MedianLeakageSpectrumUp_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MedianLeakageSpectrumUp_single_carrier_alignment_toEventFlow_injective heq)

instance MedianLeakageSpectrumUp_single_carrier_alignment_field_faithful :
    FieldFaithful MedianLeakageSpectrumUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := MedianLeakageSpectrumUp_single_carrier_alignment_fields
  field_faithful := MedianLeakageSpectrumUp_single_carrier_alignment_fields_injective

instance MedianLeakageSpectrumUp_single_carrier_alignment_nontrivial : Nontrivial MedianLeakageSpectrumUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MedianLeakageSpectrumUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MedianLeakageSpectrumUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def MedianLeakageSpectrumUp_single_carrier_alignment_taste_gate : ChapterTasteGate MedianLeakageSpectrumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  MedianLeakageSpectrumUp_single_carrier_alignment_chapter_taste_gate

theorem MedianLeakageSpectrumUp_single_carrier_alignment :
    Nonempty (ChapterTasteGate MedianLeakageSpectrumUp) ∧
      Nonempty (BHistCarrier MedianLeakageSpectrumUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨MedianLeakageSpectrumUp_single_carrier_alignment_chapter_taste_gate⟩,
      ⟨MedianLeakageSpectrumUp_single_carrier_alignment_bhist_carrier⟩⟩

end BEDC.Derived.MedianLeakageSpectrumUp
