import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRealLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRealLimitUp : Type where
  | mk (M S R D E H C P N : BHist) : CauchyRealLimitUp

def cauchyRealLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRealLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRealLimitEncodeBHist h

def cauchyRealLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRealLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRealLimitDecodeBHist tail)

private theorem CauchyRealLimitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyRealLimitDecodeBHist (cauchyRealLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRealLimitFields : CauchyRealLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealLimitUp.mk M S R D E H C P N => [M, S, R, D, E, H, C, P, N]

def cauchyRealLimitToEventFlow : CauchyRealLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRealLimitFields x).map cauchyRealLimitEncodeBHist

private def cauchyRealLimitEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyRealLimitEventAtDefault index rest

def cauchyRealLimitFromEventFlow (ef : EventFlow) : Option CauchyRealLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyRealLimitUp.mk
      (cauchyRealLimitDecodeBHist (cauchyRealLimitEventAtDefault 0 ef))
      (cauchyRealLimitDecodeBHist (cauchyRealLimitEventAtDefault 1 ef))
      (cauchyRealLimitDecodeBHist (cauchyRealLimitEventAtDefault 2 ef))
      (cauchyRealLimitDecodeBHist (cauchyRealLimitEventAtDefault 3 ef))
      (cauchyRealLimitDecodeBHist (cauchyRealLimitEventAtDefault 4 ef))
      (cauchyRealLimitDecodeBHist (cauchyRealLimitEventAtDefault 5 ef))
      (cauchyRealLimitDecodeBHist (cauchyRealLimitEventAtDefault 6 ef))
      (cauchyRealLimitDecodeBHist (cauchyRealLimitEventAtDefault 7 ef))
      (cauchyRealLimitDecodeBHist (cauchyRealLimitEventAtDefault 8 ef)))

private theorem CauchyRealLimitTasteGate_single_carrier_alignment_round_trip
    (x : CauchyRealLimitUp) :
    cauchyRealLimitFromEventFlow (cauchyRealLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M S R D E H C P N =>
      change
        some
          (CauchyRealLimitUp.mk
            (cauchyRealLimitDecodeBHist (cauchyRealLimitEncodeBHist M))
            (cauchyRealLimitDecodeBHist (cauchyRealLimitEncodeBHist S))
            (cauchyRealLimitDecodeBHist (cauchyRealLimitEncodeBHist R))
            (cauchyRealLimitDecodeBHist (cauchyRealLimitEncodeBHist D))
            (cauchyRealLimitDecodeBHist (cauchyRealLimitEncodeBHist E))
            (cauchyRealLimitDecodeBHist (cauchyRealLimitEncodeBHist H))
            (cauchyRealLimitDecodeBHist (cauchyRealLimitEncodeBHist C))
            (cauchyRealLimitDecodeBHist (cauchyRealLimitEncodeBHist P))
            (cauchyRealLimitDecodeBHist (cauchyRealLimitEncodeBHist N))) =
          some (CauchyRealLimitUp.mk M S R D E H C P N)
      rw [CauchyRealLimitTasteGate_single_carrier_alignment_decode_encode M,
        CauchyRealLimitTasteGate_single_carrier_alignment_decode_encode S,
        CauchyRealLimitTasteGate_single_carrier_alignment_decode_encode R,
        CauchyRealLimitTasteGate_single_carrier_alignment_decode_encode D,
        CauchyRealLimitTasteGate_single_carrier_alignment_decode_encode E,
        CauchyRealLimitTasteGate_single_carrier_alignment_decode_encode H,
        CauchyRealLimitTasteGate_single_carrier_alignment_decode_encode C,
        CauchyRealLimitTasteGate_single_carrier_alignment_decode_encode P,
        CauchyRealLimitTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyRealLimitTasteGate_single_carrier_alignment_injective
    {x y : CauchyRealLimitUp} :
    cauchyRealLimitToEventFlow x = cauchyRealLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRealLimitFromEventFlow (cauchyRealLimitToEventFlow x) =
        cauchyRealLimitFromEventFlow (cauchyRealLimitToEventFlow y) :=
    congrArg cauchyRealLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyRealLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyRealLimitTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyRealLimitBHistCarrier : BHistCarrier CauchyRealLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRealLimitToEventFlow
  fromEventFlow := cauchyRealLimitFromEventFlow

instance cauchyRealLimitChapterTasteGate : ChapterTasteGate CauchyRealLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRealLimitFromEventFlow (cauchyRealLimitToEventFlow x) = some x
    exact CauchyRealLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyRealLimitTasteGate_single_carrier_alignment_injective heq)

theorem CauchyRealLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRealLimitDecodeBHist (cauchyRealLimitEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyRealLimitUp) ∧
        Nonempty (ChapterTasteGate CauchyRealLimitUp) ∧
          cauchyRealLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyRealLimitTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨cauchyRealLimitBHistCarrier⟩
    · constructor
      · exact ⟨cauchyRealLimitChapterTasteGate⟩
      · rfl

end BEDC.Derived.CauchyRealLimitUp
