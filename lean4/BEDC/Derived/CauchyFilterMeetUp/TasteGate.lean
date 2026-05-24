import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterMeetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterMeetUp : Type where
  | mk (U F0 F1 B0 B1 J S R D L E H C P N : BHist) : CauchyFilterMeetUp
  deriving DecidableEq

def cauchyFilterMeetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterMeetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterMeetEncodeBHist h

def cauchyFilterMeetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterMeetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterMeetDecodeBHist tail)

private theorem CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterMeetFields : CauchyFilterMeetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterMeetUp.mk U F0 F1 B0 B1 J S R D L E H C P N =>
      [U, F0, F1, B0, B1, J, S, R, D, L, E, H, C, P, N]

def cauchyFilterMeetToEventFlow : CauchyFilterMeetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterMeetUp.mk U F0 F1 B0 B1 J S R D L E H C P N =>
      [cauchyFilterMeetEncodeBHist U,
        cauchyFilterMeetEncodeBHist F0,
        cauchyFilterMeetEncodeBHist F1,
        cauchyFilterMeetEncodeBHist B0,
        cauchyFilterMeetEncodeBHist B1,
        cauchyFilterMeetEncodeBHist J,
        cauchyFilterMeetEncodeBHist S,
        cauchyFilterMeetEncodeBHist R,
        cauchyFilterMeetEncodeBHist D,
        cauchyFilterMeetEncodeBHist L,
        cauchyFilterMeetEncodeBHist E,
        cauchyFilterMeetEncodeBHist H,
        cauchyFilterMeetEncodeBHist C,
        cauchyFilterMeetEncodeBHist P,
        cauchyFilterMeetEncodeBHist N]

private def cauchyFilterMeetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyFilterMeetEventAtDefault index rest

def cauchyFilterMeetFromEventFlow (ef : EventFlow) : Option CauchyFilterMeetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyFilterMeetUp.mk
      (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEventAtDefault 0 ef))
      (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEventAtDefault 1 ef))
      (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEventAtDefault 2 ef))
      (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEventAtDefault 3 ef))
      (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEventAtDefault 4 ef))
      (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEventAtDefault 5 ef))
      (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEventAtDefault 6 ef))
      (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEventAtDefault 7 ef))
      (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEventAtDefault 8 ef))
      (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEventAtDefault 9 ef))
      (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEventAtDefault 10 ef))
      (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEventAtDefault 11 ef))
      (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEventAtDefault 12 ef))
      (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEventAtDefault 13 ef))
      (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEventAtDefault 14 ef)))

private theorem CauchyFilterMeetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyFilterMeetUp,
      cauchyFilterMeetFromEventFlow (cauchyFilterMeetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U F0 F1 B0 B1 J S R D L E H C P N =>
      change
        some
          (CauchyFilterMeetUp.mk
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist U))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist F0))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist F1))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist B0))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist B1))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist J))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist S))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist R))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist D))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist L))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist E))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist H))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist C))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist P))
            (cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist N))) =
          some (CauchyFilterMeetUp.mk U F0 F1 B0 B1 J S R D L E H C P N)
      rw [CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode U,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode F0,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode F1,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode B0,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode B1,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode J,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode S,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode R,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode D,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode L,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode E,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode H,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode C,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode P,
        CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyFilterMeetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyFilterMeetUp} :
    cauchyFilterMeetToEventFlow x = cauchyFilterMeetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyFilterMeetFromEventFlow (cauchyFilterMeetToEventFlow x) =
        cauchyFilterMeetFromEventFlow (cauchyFilterMeetToEventFlow y) :=
    congrArg cauchyFilterMeetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyFilterMeetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyFilterMeetTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyFilterMeetBHistCarrier : BHistCarrier CauchyFilterMeetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterMeetToEventFlow
  fromEventFlow := cauchyFilterMeetFromEventFlow

instance cauchyFilterMeetChapterTasteGate : ChapterTasteGate CauchyFilterMeetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyFilterMeetFromEventFlow (cauchyFilterMeetToEventFlow x) = some x
    exact CauchyFilterMeetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyFilterMeetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyFilterMeetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyFilterMeetChapterTasteGate

theorem CauchyFilterMeetTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyFilterMeetDecodeBHist (cauchyFilterMeetEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyFilterMeetUp) ∧
        Nonempty (ChapterTasteGate CauchyFilterMeetUp) ∧
          cauchyFilterMeetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyFilterMeetTasteGate_single_carrier_alignment_decode_encode,
      ⟨cauchyFilterMeetBHistCarrier⟩,
      ⟨cauchyFilterMeetChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyFilterMeetUp
