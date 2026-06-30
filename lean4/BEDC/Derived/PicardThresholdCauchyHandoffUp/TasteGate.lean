import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PicardThresholdCauchyHandoffUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PicardThresholdCauchyHandoffUp : Type where
  | mk (B I E M R K S T C P N : BHist) : PicardThresholdCauchyHandoffUp
  deriving DecidableEq

def picardThresholdCauchyHandoffEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: picardThresholdCauchyHandoffEncodeBHist h
  | BHist.e1 h => BMark.b1 :: picardThresholdCauchyHandoffEncodeBHist h

def picardThresholdCauchyHandoffDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (picardThresholdCauchyHandoffDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (picardThresholdCauchyHandoffDecodeBHist tail)

private theorem picardThresholdCauchyHandoff_decode_encode_bhist :
    ∀ h : BHist,
      picardThresholdCauchyHandoffDecodeBHist
        (picardThresholdCauchyHandoffEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def picardThresholdCauchyHandoffToEventFlow :
    PicardThresholdCauchyHandoffUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PicardThresholdCauchyHandoffUp.mk B I E M R K S T C P N =>
      [picardThresholdCauchyHandoffEncodeBHist B,
        picardThresholdCauchyHandoffEncodeBHist I,
        picardThresholdCauchyHandoffEncodeBHist E,
        picardThresholdCauchyHandoffEncodeBHist M,
        picardThresholdCauchyHandoffEncodeBHist R,
        picardThresholdCauchyHandoffEncodeBHist K,
        picardThresholdCauchyHandoffEncodeBHist S,
        picardThresholdCauchyHandoffEncodeBHist T,
        picardThresholdCauchyHandoffEncodeBHist C,
        picardThresholdCauchyHandoffEncodeBHist P,
        picardThresholdCauchyHandoffEncodeBHist N]

private def picardThresholdCauchyHandoffEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      picardThresholdCauchyHandoffEventAtDefault index rest

def picardThresholdCauchyHandoffFromEventFlow
    (ef : EventFlow) : Option PicardThresholdCauchyHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PicardThresholdCauchyHandoffUp.mk
      (picardThresholdCauchyHandoffDecodeBHist
        (picardThresholdCauchyHandoffEventAtDefault 0 ef))
      (picardThresholdCauchyHandoffDecodeBHist
        (picardThresholdCauchyHandoffEventAtDefault 1 ef))
      (picardThresholdCauchyHandoffDecodeBHist
        (picardThresholdCauchyHandoffEventAtDefault 2 ef))
      (picardThresholdCauchyHandoffDecodeBHist
        (picardThresholdCauchyHandoffEventAtDefault 3 ef))
      (picardThresholdCauchyHandoffDecodeBHist
        (picardThresholdCauchyHandoffEventAtDefault 4 ef))
      (picardThresholdCauchyHandoffDecodeBHist
        (picardThresholdCauchyHandoffEventAtDefault 5 ef))
      (picardThresholdCauchyHandoffDecodeBHist
        (picardThresholdCauchyHandoffEventAtDefault 6 ef))
      (picardThresholdCauchyHandoffDecodeBHist
        (picardThresholdCauchyHandoffEventAtDefault 7 ef))
      (picardThresholdCauchyHandoffDecodeBHist
        (picardThresholdCauchyHandoffEventAtDefault 8 ef))
      (picardThresholdCauchyHandoffDecodeBHist
        (picardThresholdCauchyHandoffEventAtDefault 9 ef))
      (picardThresholdCauchyHandoffDecodeBHist
        (picardThresholdCauchyHandoffEventAtDefault 10 ef)))

private theorem picardThresholdCauchyHandoff_round_trip :
    ∀ x : PicardThresholdCauchyHandoffUp,
      picardThresholdCauchyHandoffFromEventFlow
        (picardThresholdCauchyHandoffToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B I E M R K S T C P N =>
      change
        some
            (PicardThresholdCauchyHandoffUp.mk
              (picardThresholdCauchyHandoffDecodeBHist
                (picardThresholdCauchyHandoffEncodeBHist B))
              (picardThresholdCauchyHandoffDecodeBHist
                (picardThresholdCauchyHandoffEncodeBHist I))
              (picardThresholdCauchyHandoffDecodeBHist
                (picardThresholdCauchyHandoffEncodeBHist E))
              (picardThresholdCauchyHandoffDecodeBHist
                (picardThresholdCauchyHandoffEncodeBHist M))
              (picardThresholdCauchyHandoffDecodeBHist
                (picardThresholdCauchyHandoffEncodeBHist R))
              (picardThresholdCauchyHandoffDecodeBHist
                (picardThresholdCauchyHandoffEncodeBHist K))
              (picardThresholdCauchyHandoffDecodeBHist
                (picardThresholdCauchyHandoffEncodeBHist S))
              (picardThresholdCauchyHandoffDecodeBHist
                (picardThresholdCauchyHandoffEncodeBHist T))
              (picardThresholdCauchyHandoffDecodeBHist
                (picardThresholdCauchyHandoffEncodeBHist C))
              (picardThresholdCauchyHandoffDecodeBHist
                (picardThresholdCauchyHandoffEncodeBHist P))
              (picardThresholdCauchyHandoffDecodeBHist
                (picardThresholdCauchyHandoffEncodeBHist N))) =
          some (PicardThresholdCauchyHandoffUp.mk B I E M R K S T C P N)
      rw [picardThresholdCauchyHandoff_decode_encode_bhist B,
        picardThresholdCauchyHandoff_decode_encode_bhist I,
        picardThresholdCauchyHandoff_decode_encode_bhist E,
        picardThresholdCauchyHandoff_decode_encode_bhist M,
        picardThresholdCauchyHandoff_decode_encode_bhist R,
        picardThresholdCauchyHandoff_decode_encode_bhist K,
        picardThresholdCauchyHandoff_decode_encode_bhist S,
        picardThresholdCauchyHandoff_decode_encode_bhist T,
        picardThresholdCauchyHandoff_decode_encode_bhist C,
        picardThresholdCauchyHandoff_decode_encode_bhist P,
        picardThresholdCauchyHandoff_decode_encode_bhist N]

private theorem picardThresholdCauchyHandoffToEventFlow_injective
    {x y : PicardThresholdCauchyHandoffUp} :
    picardThresholdCauchyHandoffToEventFlow x =
        picardThresholdCauchyHandoffToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      picardThresholdCauchyHandoffFromEventFlow
          (picardThresholdCauchyHandoffToEventFlow x) =
        picardThresholdCauchyHandoffFromEventFlow
          (picardThresholdCauchyHandoffToEventFlow y) :=
    congrArg picardThresholdCauchyHandoffFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (picardThresholdCauchyHandoff_round_trip x).symm
      (Eq.trans hread (picardThresholdCauchyHandoff_round_trip y)))

def picardThresholdCauchyHandoffFields :
    PicardThresholdCauchyHandoffUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PicardThresholdCauchyHandoffUp.mk B I E M R K S T C P N =>
      [B, I, E, M, R, K, S, T, C, P, N]

private theorem picardThresholdCauchyHandoff_fields_faithful :
    ∀ x y : PicardThresholdCauchyHandoffUp,
      picardThresholdCauchyHandoffFields x =
        picardThresholdCauchyHandoffFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk B I E M R K S T C P N =>
      cases y with
      | mk B' I' E' M' R' K' S' T' C' P' N' =>
          simp only [picardThresholdCauchyHandoffFields] at h
          cases h
          rfl

instance picardThresholdCauchyHandoffBHistCarrier :
    BHistCarrier PicardThresholdCauchyHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := picardThresholdCauchyHandoffToEventFlow
  fromEventFlow := picardThresholdCauchyHandoffFromEventFlow

instance picardThresholdCauchyHandoffChapterTasteGate :
    ChapterTasteGate PicardThresholdCauchyHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      picardThresholdCauchyHandoffFromEventFlow
        (picardThresholdCauchyHandoffToEventFlow x) = some x
    exact picardThresholdCauchyHandoff_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (picardThresholdCauchyHandoffToEventFlow_injective heq)

instance picardThresholdCauchyHandoffFieldFaithful :
    FieldFaithful PicardThresholdCauchyHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := picardThresholdCauchyHandoffFields
  field_faithful := picardThresholdCauchyHandoff_fields_faithful

instance picardThresholdCauchyHandoffNontrivial :
    BEDC.Meta.TasteGate.Nontrivial PicardThresholdCauchyHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PicardThresholdCauchyHandoffUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      PicardThresholdCauchyHandoffUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PicardThresholdCauchyHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  picardThresholdCauchyHandoffChapterTasteGate

theorem PicardThresholdCauchyHandoffTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      picardThresholdCauchyHandoffDecodeBHist
        (picardThresholdCauchyHandoffEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier PicardThresholdCauchyHandoffUp) ∧
        Nonempty (ChapterTasteGate PicardThresholdCauchyHandoffUp) ∧
          picardThresholdCauchyHandoffEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨picardThresholdCauchyHandoff_decode_encode_bhist,
      ⟨⟨picardThresholdCauchyHandoffBHistCarrier⟩,
        ⟨picardThresholdCauchyHandoffChapterTasteGate⟩,
        rfl⟩⟩

end BEDC.Derived.PicardThresholdCauchyHandoffUp
