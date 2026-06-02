import BEDC.Derived.CauchyContinuousMapUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def cauchyContinuousMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyContinuousMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyContinuousMapEncodeBHist h

def cauchyContinuousMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyContinuousMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyContinuousMapDecodeBHist tail)

private theorem CauchyContinuousMapTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyContinuousMapDecodeBHist (cauchyContinuousMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyContinuousMapToEventFlow : BEDC.Derived.CauchyContinuousMapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.CauchyContinuousMapUp.mk W R D E H C P N =>
      [cauchyContinuousMapEncodeBHist W,
        cauchyContinuousMapEncodeBHist R,
        cauchyContinuousMapEncodeBHist D,
        cauchyContinuousMapEncodeBHist E,
        cauchyContinuousMapEncodeBHist H,
        cauchyContinuousMapEncodeBHist C,
        cauchyContinuousMapEncodeBHist P,
        cauchyContinuousMapEncodeBHist N]

private def cauchyContinuousMapEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyContinuousMapEventAtDefault index rest

def cauchyContinuousMapDecodeEventFlow
    (ef : EventFlow) : BEDC.Derived.CauchyContinuousMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.CauchyContinuousMapUp.mk
    (cauchyContinuousMapDecodeBHist (cauchyContinuousMapEventAtDefault 0 ef))
    (cauchyContinuousMapDecodeBHist (cauchyContinuousMapEventAtDefault 1 ef))
    (cauchyContinuousMapDecodeBHist (cauchyContinuousMapEventAtDefault 2 ef))
    (cauchyContinuousMapDecodeBHist (cauchyContinuousMapEventAtDefault 3 ef))
    (cauchyContinuousMapDecodeBHist (cauchyContinuousMapEventAtDefault 4 ef))
    (cauchyContinuousMapDecodeBHist (cauchyContinuousMapEventAtDefault 5 ef))
    (cauchyContinuousMapDecodeBHist (cauchyContinuousMapEventAtDefault 6 ef))
    (cauchyContinuousMapDecodeBHist (cauchyContinuousMapEventAtDefault 7 ef))

def cauchyContinuousMapFromEventFlow
    (ef : EventFlow) : Option BEDC.Derived.CauchyContinuousMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some (cauchyContinuousMapDecodeEventFlow ef)

private theorem CauchyContinuousMapTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BEDC.Derived.CauchyContinuousMapUp,
      cauchyContinuousMapFromEventFlow (cauchyContinuousMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W R D E H C P N =>
      change
        some
          (BEDC.Derived.CauchyContinuousMapUp.mk
            (cauchyContinuousMapDecodeBHist (cauchyContinuousMapEncodeBHist W))
            (cauchyContinuousMapDecodeBHist (cauchyContinuousMapEncodeBHist R))
            (cauchyContinuousMapDecodeBHist (cauchyContinuousMapEncodeBHist D))
            (cauchyContinuousMapDecodeBHist (cauchyContinuousMapEncodeBHist E))
            (cauchyContinuousMapDecodeBHist (cauchyContinuousMapEncodeBHist H))
            (cauchyContinuousMapDecodeBHist (cauchyContinuousMapEncodeBHist C))
            (cauchyContinuousMapDecodeBHist (cauchyContinuousMapEncodeBHist P))
            (cauchyContinuousMapDecodeBHist (cauchyContinuousMapEncodeBHist N))) =
          some (BEDC.Derived.CauchyContinuousMapUp.mk W R D E H C P N)
      rw [CauchyContinuousMapTasteGate_single_carrier_alignment_decode_encode W,
        CauchyContinuousMapTasteGate_single_carrier_alignment_decode_encode R,
        CauchyContinuousMapTasteGate_single_carrier_alignment_decode_encode D,
        CauchyContinuousMapTasteGate_single_carrier_alignment_decode_encode E,
        CauchyContinuousMapTasteGate_single_carrier_alignment_decode_encode H,
        CauchyContinuousMapTasteGate_single_carrier_alignment_decode_encode C,
        CauchyContinuousMapTasteGate_single_carrier_alignment_decode_encode P,
        CauchyContinuousMapTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyContinuousMapTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BEDC.Derived.CauchyContinuousMapUp} :
    cauchyContinuousMapToEventFlow x = cauchyContinuousMapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyContinuousMapFromEventFlow (cauchyContinuousMapToEventFlow x) =
        cauchyContinuousMapFromEventFlow (cauchyContinuousMapToEventFlow y) :=
    congrArg cauchyContinuousMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyContinuousMapTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyContinuousMapTasteGate_single_carrier_alignment_round_trip y)))

instance CauchyContinuousMapTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier BEDC.Derived.CauchyContinuousMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyContinuousMapToEventFlow
  fromEventFlow := cauchyContinuousMapFromEventFlow

instance CauchyContinuousMapTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate BEDC.Derived.CauchyContinuousMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyContinuousMapFromEventFlow (cauchyContinuousMapToEventFlow x) = some x
    exact CauchyContinuousMapTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyContinuousMapTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyContinuousMapTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyContinuousMapDecodeBHist (cauchyContinuousMapEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BEDC.Derived.CauchyContinuousMapUp) ∧
        Nonempty (ChapterTasteGate BEDC.Derived.CauchyContinuousMapUp) ∧
          cauchyContinuousMapEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨CauchyContinuousMapTasteGate_single_carrier_alignment_decode_encode,
      ⟨CauchyContinuousMapTasteGate_single_carrier_alignment_BHistCarrier⟩,
      ⟨CauchyContinuousMapTasteGate_single_carrier_alignment_ChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyContinuousMapUp
