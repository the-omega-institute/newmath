import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DarbouxContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DarbouxContinuityUp : Type where
  | mk (I G V D R E H C P N : BHist) : DarbouxContinuityUp
  deriving DecidableEq

def darbouxContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: darbouxContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: darbouxContinuityEncodeBHist h

def darbouxContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (darbouxContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (darbouxContinuityDecodeBHist tail)

private theorem DarbouxContinuityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, darbouxContinuityDecodeBHist (darbouxContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def darbouxContinuityToEventFlow : DarbouxContinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DarbouxContinuityUp.mk I G V D R E H C P N =>
      [[BMark.b0],
        darbouxContinuityEncodeBHist I,
        [BMark.b1, BMark.b0],
        darbouxContinuityEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b0],
        darbouxContinuityEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        darbouxContinuityEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        darbouxContinuityEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        darbouxContinuityEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        darbouxContinuityEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        darbouxContinuityEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        darbouxContinuityEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        darbouxContinuityEncodeBHist N]

private def darbouxContinuityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => darbouxContinuityEventAtDefault index rest

def darbouxContinuityFromEventFlow (ef : EventFlow) : Option DarbouxContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DarbouxContinuityUp.mk
      (darbouxContinuityDecodeBHist (darbouxContinuityEventAtDefault 1 ef))
      (darbouxContinuityDecodeBHist (darbouxContinuityEventAtDefault 3 ef))
      (darbouxContinuityDecodeBHist (darbouxContinuityEventAtDefault 5 ef))
      (darbouxContinuityDecodeBHist (darbouxContinuityEventAtDefault 7 ef))
      (darbouxContinuityDecodeBHist (darbouxContinuityEventAtDefault 9 ef))
      (darbouxContinuityDecodeBHist (darbouxContinuityEventAtDefault 11 ef))
      (darbouxContinuityDecodeBHist (darbouxContinuityEventAtDefault 13 ef))
      (darbouxContinuityDecodeBHist (darbouxContinuityEventAtDefault 15 ef))
      (darbouxContinuityDecodeBHist (darbouxContinuityEventAtDefault 17 ef))
      (darbouxContinuityDecodeBHist (darbouxContinuityEventAtDefault 19 ef)))

private theorem DarbouxContinuityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DarbouxContinuityUp,
      darbouxContinuityFromEventFlow (darbouxContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I G V D R E H C P N =>
      change
        some
          (DarbouxContinuityUp.mk
            (darbouxContinuityDecodeBHist (darbouxContinuityEncodeBHist I))
            (darbouxContinuityDecodeBHist (darbouxContinuityEncodeBHist G))
            (darbouxContinuityDecodeBHist (darbouxContinuityEncodeBHist V))
            (darbouxContinuityDecodeBHist (darbouxContinuityEncodeBHist D))
            (darbouxContinuityDecodeBHist (darbouxContinuityEncodeBHist R))
            (darbouxContinuityDecodeBHist (darbouxContinuityEncodeBHist E))
            (darbouxContinuityDecodeBHist (darbouxContinuityEncodeBHist H))
            (darbouxContinuityDecodeBHist (darbouxContinuityEncodeBHist C))
            (darbouxContinuityDecodeBHist (darbouxContinuityEncodeBHist P))
            (darbouxContinuityDecodeBHist (darbouxContinuityEncodeBHist N))) =
          some (DarbouxContinuityUp.mk I G V D R E H C P N)
      rw [DarbouxContinuityTasteGate_single_carrier_alignment_decode_encode I,
        DarbouxContinuityTasteGate_single_carrier_alignment_decode_encode G,
        DarbouxContinuityTasteGate_single_carrier_alignment_decode_encode V,
        DarbouxContinuityTasteGate_single_carrier_alignment_decode_encode D,
        DarbouxContinuityTasteGate_single_carrier_alignment_decode_encode R,
        DarbouxContinuityTasteGate_single_carrier_alignment_decode_encode E,
        DarbouxContinuityTasteGate_single_carrier_alignment_decode_encode H,
        DarbouxContinuityTasteGate_single_carrier_alignment_decode_encode C,
        DarbouxContinuityTasteGate_single_carrier_alignment_decode_encode P,
        DarbouxContinuityTasteGate_single_carrier_alignment_decode_encode N]

private theorem DarbouxContinuityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DarbouxContinuityUp} :
    darbouxContinuityToEventFlow x = darbouxContinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      darbouxContinuityFromEventFlow (darbouxContinuityToEventFlow x) =
        darbouxContinuityFromEventFlow (darbouxContinuityToEventFlow y) :=
    congrArg darbouxContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DarbouxContinuityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DarbouxContinuityTasteGate_single_carrier_alignment_round_trip y)))

instance darbouxContinuityBHistCarrier : BHistCarrier DarbouxContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := darbouxContinuityToEventFlow
  fromEventFlow := darbouxContinuityFromEventFlow

instance darbouxContinuityChapterTasteGate : ChapterTasteGate DarbouxContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change darbouxContinuityFromEventFlow (darbouxContinuityToEventFlow x) = some x
    exact DarbouxContinuityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DarbouxContinuityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate DarbouxContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  darbouxContinuityChapterTasteGate

theorem DarbouxContinuityTasteGate_single_carrier_alignment :
    (∀ h : BHist, darbouxContinuityDecodeBHist (darbouxContinuityEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DarbouxContinuityUp) ∧
        Nonempty (ChapterTasteGate DarbouxContinuityUp) ∧
          darbouxContinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨DarbouxContinuityTasteGate_single_carrier_alignment_decode_encode,
      ⟨darbouxContinuityBHistCarrier⟩,
      ⟨darbouxContinuityChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.DarbouxContinuityUp
