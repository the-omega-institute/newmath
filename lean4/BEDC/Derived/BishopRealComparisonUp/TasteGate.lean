import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRealComparisonUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRealComparisonUp : Type where
  | mk
      (bishop completion located dedekind realSeal readback transport provenance
        name : BHist) :
      BishopRealComparisonUp
  deriving DecidableEq

def bishopRealComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRealComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRealComparisonEncodeBHist h

def bishopRealComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRealComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRealComparisonDecodeBHist tail)

private theorem bishopRealComparison_decode_encode_bhist :
    ∀ h : BHist, bishopRealComparisonDecodeBHist (bishopRealComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRealComparisonFields : BishopRealComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRealComparisonUp.mk bishop completion located dedekind realSeal readback transport
      provenance name =>
      [bishop, completion, located, dedekind, realSeal, readback, transport, provenance, name]

def bishopRealComparisonToEventFlow : BishopRealComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopRealComparisonFields x).map bishopRealComparisonEncodeBHist

private def bishopRealComparisonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopRealComparisonEventAtDefault index rest

def bishopRealComparisonFromEventFlow (ef : EventFlow) : Option BishopRealComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopRealComparisonUp.mk
      (bishopRealComparisonDecodeBHist (bishopRealComparisonEventAtDefault 0 ef))
      (bishopRealComparisonDecodeBHist (bishopRealComparisonEventAtDefault 1 ef))
      (bishopRealComparisonDecodeBHist (bishopRealComparisonEventAtDefault 2 ef))
      (bishopRealComparisonDecodeBHist (bishopRealComparisonEventAtDefault 3 ef))
      (bishopRealComparisonDecodeBHist (bishopRealComparisonEventAtDefault 4 ef))
      (bishopRealComparisonDecodeBHist (bishopRealComparisonEventAtDefault 5 ef))
      (bishopRealComparisonDecodeBHist (bishopRealComparisonEventAtDefault 6 ef))
      (bishopRealComparisonDecodeBHist (bishopRealComparisonEventAtDefault 7 ef))
      (bishopRealComparisonDecodeBHist (bishopRealComparisonEventAtDefault 8 ef)))

private theorem bishopRealComparison_round_trip :
    ∀ x : BishopRealComparisonUp,
      bishopRealComparisonFromEventFlow (bishopRealComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk bishop completion located dedekind realSeal readback transport provenance name =>
      change
        some
          (BishopRealComparisonUp.mk
            (bishopRealComparisonDecodeBHist (bishopRealComparisonEncodeBHist bishop))
            (bishopRealComparisonDecodeBHist (bishopRealComparisonEncodeBHist completion))
            (bishopRealComparisonDecodeBHist (bishopRealComparisonEncodeBHist located))
            (bishopRealComparisonDecodeBHist (bishopRealComparisonEncodeBHist dedekind))
            (bishopRealComparisonDecodeBHist (bishopRealComparisonEncodeBHist realSeal))
            (bishopRealComparisonDecodeBHist (bishopRealComparisonEncodeBHist readback))
            (bishopRealComparisonDecodeBHist (bishopRealComparisonEncodeBHist transport))
            (bishopRealComparisonDecodeBHist (bishopRealComparisonEncodeBHist provenance))
            (bishopRealComparisonDecodeBHist (bishopRealComparisonEncodeBHist name))) =
          some
            (BishopRealComparisonUp.mk bishop completion located dedekind realSeal readback
              transport provenance name)
      rw [bishopRealComparison_decode_encode_bhist bishop,
        bishopRealComparison_decode_encode_bhist completion,
        bishopRealComparison_decode_encode_bhist located,
        bishopRealComparison_decode_encode_bhist dedekind,
        bishopRealComparison_decode_encode_bhist realSeal,
        bishopRealComparison_decode_encode_bhist readback,
        bishopRealComparison_decode_encode_bhist transport,
        bishopRealComparison_decode_encode_bhist provenance,
        bishopRealComparison_decode_encode_bhist name]

private theorem bishopRealComparisonToEventFlow_injective {x y : BishopRealComparisonUp} :
    bishopRealComparisonToEventFlow x = bishopRealComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRealComparisonFromEventFlow (bishopRealComparisonToEventFlow x) =
        bishopRealComparisonFromEventFlow (bishopRealComparisonToEventFlow y) :=
    congrArg bishopRealComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopRealComparison_round_trip x).symm
      (Eq.trans hread (bishopRealComparison_round_trip y)))

instance bishopRealComparisonBHistCarrier : BHistCarrier BishopRealComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRealComparisonToEventFlow
  fromEventFlow := bishopRealComparisonFromEventFlow

instance bishopRealComparisonChapterTasteGate : ChapterTasteGate BishopRealComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopRealComparisonFromEventFlow (bishopRealComparisonToEventFlow x) = some x
    exact bishopRealComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopRealComparisonToEventFlow_injective heq)

theorem BishopRealComparisonTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BishopRealComparisonUp) ∧
      Nonempty (ChapterTasteGate BishopRealComparisonUp) ∧
        ∃ x : BishopRealComparisonUp,
          BHistCarrier.toEventFlow x =
            bishopRealComparisonToEventFlow
              (BishopRealComparisonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨bishopRealComparisonBHistCarrier⟩,
      ⟨⟨bishopRealComparisonChapterTasteGate⟩,
        ⟨BishopRealComparisonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
          rfl⟩⟩⟩

end BEDC.Derived.BishopRealComparisonUp.TasteGate
