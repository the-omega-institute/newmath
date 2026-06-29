import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusCompletenessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusCompletenessUp : Type where
  | mk (M E K W R D L H C P N : BHist) : CauchyModulusCompletenessUp
  deriving DecidableEq

def cauchyModulusCompletenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusCompletenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusCompletenessEncodeBHist h

def cauchyModulusCompletenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusCompletenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusCompletenessDecodeBHist tail)

private theorem CauchyModulusCompletenessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyModulusCompletenessDecodeBHist
        (cauchyModulusCompletenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusCompletenessToEventFlow : CauchyModulusCompletenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusCompletenessUp.mk M E K W R D L H C P N =>
      [cauchyModulusCompletenessEncodeBHist M,
        cauchyModulusCompletenessEncodeBHist E,
        cauchyModulusCompletenessEncodeBHist K,
        cauchyModulusCompletenessEncodeBHist W,
        cauchyModulusCompletenessEncodeBHist R,
        cauchyModulusCompletenessEncodeBHist D,
        cauchyModulusCompletenessEncodeBHist L,
        cauchyModulusCompletenessEncodeBHist H,
        cauchyModulusCompletenessEncodeBHist C,
        cauchyModulusCompletenessEncodeBHist P,
        cauchyModulusCompletenessEncodeBHist N]

private def cauchyModulusCompletenessEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyModulusCompletenessEventAt index rest

def cauchyModulusCompletenessFromEventFlow
    (ef : EventFlow) : Option CauchyModulusCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyModulusCompletenessUp.mk
      (cauchyModulusCompletenessDecodeBHist (cauchyModulusCompletenessEventAt 0 ef))
      (cauchyModulusCompletenessDecodeBHist (cauchyModulusCompletenessEventAt 1 ef))
      (cauchyModulusCompletenessDecodeBHist (cauchyModulusCompletenessEventAt 2 ef))
      (cauchyModulusCompletenessDecodeBHist (cauchyModulusCompletenessEventAt 3 ef))
      (cauchyModulusCompletenessDecodeBHist (cauchyModulusCompletenessEventAt 4 ef))
      (cauchyModulusCompletenessDecodeBHist (cauchyModulusCompletenessEventAt 5 ef))
      (cauchyModulusCompletenessDecodeBHist (cauchyModulusCompletenessEventAt 6 ef))
      (cauchyModulusCompletenessDecodeBHist (cauchyModulusCompletenessEventAt 7 ef))
      (cauchyModulusCompletenessDecodeBHist (cauchyModulusCompletenessEventAt 8 ef))
      (cauchyModulusCompletenessDecodeBHist (cauchyModulusCompletenessEventAt 9 ef))
      (cauchyModulusCompletenessDecodeBHist (cauchyModulusCompletenessEventAt 10 ef)))

private theorem CauchyModulusCompletenessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyModulusCompletenessUp,
      cauchyModulusCompletenessFromEventFlow
        (cauchyModulusCompletenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M E K W R D L H C P N =>
      change
        some
          (CauchyModulusCompletenessUp.mk
            (cauchyModulusCompletenessDecodeBHist
              (cauchyModulusCompletenessEncodeBHist M))
            (cauchyModulusCompletenessDecodeBHist
              (cauchyModulusCompletenessEncodeBHist E))
            (cauchyModulusCompletenessDecodeBHist
              (cauchyModulusCompletenessEncodeBHist K))
            (cauchyModulusCompletenessDecodeBHist
              (cauchyModulusCompletenessEncodeBHist W))
            (cauchyModulusCompletenessDecodeBHist
              (cauchyModulusCompletenessEncodeBHist R))
            (cauchyModulusCompletenessDecodeBHist
              (cauchyModulusCompletenessEncodeBHist D))
            (cauchyModulusCompletenessDecodeBHist
              (cauchyModulusCompletenessEncodeBHist L))
            (cauchyModulusCompletenessDecodeBHist
              (cauchyModulusCompletenessEncodeBHist H))
            (cauchyModulusCompletenessDecodeBHist
              (cauchyModulusCompletenessEncodeBHist C))
            (cauchyModulusCompletenessDecodeBHist
              (cauchyModulusCompletenessEncodeBHist P))
            (cauchyModulusCompletenessDecodeBHist
              (cauchyModulusCompletenessEncodeBHist N))) =
          some (CauchyModulusCompletenessUp.mk M E K W R D L H C P N)
      rw [CauchyModulusCompletenessTasteGate_single_carrier_alignment_decode_encode M,
        CauchyModulusCompletenessTasteGate_single_carrier_alignment_decode_encode E,
        CauchyModulusCompletenessTasteGate_single_carrier_alignment_decode_encode K,
        CauchyModulusCompletenessTasteGate_single_carrier_alignment_decode_encode W,
        CauchyModulusCompletenessTasteGate_single_carrier_alignment_decode_encode R,
        CauchyModulusCompletenessTasteGate_single_carrier_alignment_decode_encode D,
        CauchyModulusCompletenessTasteGate_single_carrier_alignment_decode_encode L,
        CauchyModulusCompletenessTasteGate_single_carrier_alignment_decode_encode H,
        CauchyModulusCompletenessTasteGate_single_carrier_alignment_decode_encode C,
        CauchyModulusCompletenessTasteGate_single_carrier_alignment_decode_encode P,
        CauchyModulusCompletenessTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyModulusCompletenessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyModulusCompletenessUp} :
    cauchyModulusCompletenessToEventFlow x =
      cauchyModulusCompletenessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusCompletenessFromEventFlow (cauchyModulusCompletenessToEventFlow x) =
        cauchyModulusCompletenessFromEventFlow (cauchyModulusCompletenessToEventFlow y) :=
    congrArg cauchyModulusCompletenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyModulusCompletenessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyModulusCompletenessTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyModulusCompletenessBHistCarrier : BHistCarrier CauchyModulusCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusCompletenessToEventFlow
  fromEventFlow := cauchyModulusCompletenessFromEventFlow

instance cauchyModulusCompletenessChapterTasteGate :
    ChapterTasteGate CauchyModulusCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyModulusCompletenessFromEventFlow
      (cauchyModulusCompletenessToEventFlow x) = some x
    exact CauchyModulusCompletenessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyModulusCompletenessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyModulusCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyModulusCompletenessChapterTasteGate

theorem CauchyModulusCompletenessTasteGate_single_carrier_alignment :
    cauchyModulusCompletenessFromEventFlow
        (cauchyModulusCompletenessToEventFlow
          (CauchyModulusCompletenessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty)) =
      some
        (CauchyModulusCompletenessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    CauchyModulusCompletenessTasteGate_single_carrier_alignment_round_trip
      (CauchyModulusCompletenessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty)

end BEDC.Derived.CauchyModulusCompletenessUp.TasteGate
