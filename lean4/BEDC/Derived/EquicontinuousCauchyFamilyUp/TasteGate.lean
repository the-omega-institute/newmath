import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EquicontinuousCauchyFamilyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EquicontinuousCauchyFamilyUp : Type where
  | mk (K U M T W R D A H C P N : BHist) : EquicontinuousCauchyFamilyUp
  deriving DecidableEq

def equicontinuousCauchyFamilyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: equicontinuousCauchyFamilyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: equicontinuousCauchyFamilyEncodeBHist h

def equicontinuousCauchyFamilyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (equicontinuousCauchyFamilyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (equicontinuousCauchyFamilyDecodeBHist tail)

private theorem EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      equicontinuousCauchyFamilyDecodeBHist
          (equicontinuousCauchyFamilyEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def equicontinuousCauchyFamilyFields :
    EquicontinuousCauchyFamilyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EquicontinuousCauchyFamilyUp.mk K U M T W R D A H C P N =>
      [K, U, M, T, W, R, D, A, H, C, P, N]

def equicontinuousCauchyFamilyToEventFlow :
    EquicontinuousCauchyFamilyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (equicontinuousCauchyFamilyFields x).map equicontinuousCauchyFamilyEncodeBHist

private def equicontinuousCauchyFamilyEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => equicontinuousCauchyFamilyEventAt index rest

def equicontinuousCauchyFamilyFromEventFlow (ef : EventFlow) :
    Option EquicontinuousCauchyFamilyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EquicontinuousCauchyFamilyUp.mk
      (equicontinuousCauchyFamilyDecodeBHist (equicontinuousCauchyFamilyEventAt 0 ef))
      (equicontinuousCauchyFamilyDecodeBHist (equicontinuousCauchyFamilyEventAt 1 ef))
      (equicontinuousCauchyFamilyDecodeBHist (equicontinuousCauchyFamilyEventAt 2 ef))
      (equicontinuousCauchyFamilyDecodeBHist (equicontinuousCauchyFamilyEventAt 3 ef))
      (equicontinuousCauchyFamilyDecodeBHist (equicontinuousCauchyFamilyEventAt 4 ef))
      (equicontinuousCauchyFamilyDecodeBHist (equicontinuousCauchyFamilyEventAt 5 ef))
      (equicontinuousCauchyFamilyDecodeBHist (equicontinuousCauchyFamilyEventAt 6 ef))
      (equicontinuousCauchyFamilyDecodeBHist (equicontinuousCauchyFamilyEventAt 7 ef))
      (equicontinuousCauchyFamilyDecodeBHist (equicontinuousCauchyFamilyEventAt 8 ef))
      (equicontinuousCauchyFamilyDecodeBHist (equicontinuousCauchyFamilyEventAt 9 ef))
      (equicontinuousCauchyFamilyDecodeBHist (equicontinuousCauchyFamilyEventAt 10 ef))
      (equicontinuousCauchyFamilyDecodeBHist (equicontinuousCauchyFamilyEventAt 11 ef)))

private theorem EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_round_trip
    (x : EquicontinuousCauchyFamilyUp) :
    equicontinuousCauchyFamilyFromEventFlow
        (equicontinuousCauchyFamilyToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K U M T W R D A H C P N =>
      change
        some
          (EquicontinuousCauchyFamilyUp.mk
            (equicontinuousCauchyFamilyDecodeBHist
              (equicontinuousCauchyFamilyEncodeBHist K))
            (equicontinuousCauchyFamilyDecodeBHist
              (equicontinuousCauchyFamilyEncodeBHist U))
            (equicontinuousCauchyFamilyDecodeBHist
              (equicontinuousCauchyFamilyEncodeBHist M))
            (equicontinuousCauchyFamilyDecodeBHist
              (equicontinuousCauchyFamilyEncodeBHist T))
            (equicontinuousCauchyFamilyDecodeBHist
              (equicontinuousCauchyFamilyEncodeBHist W))
            (equicontinuousCauchyFamilyDecodeBHist
              (equicontinuousCauchyFamilyEncodeBHist R))
            (equicontinuousCauchyFamilyDecodeBHist
              (equicontinuousCauchyFamilyEncodeBHist D))
            (equicontinuousCauchyFamilyDecodeBHist
              (equicontinuousCauchyFamilyEncodeBHist A))
            (equicontinuousCauchyFamilyDecodeBHist
              (equicontinuousCauchyFamilyEncodeBHist H))
            (equicontinuousCauchyFamilyDecodeBHist
              (equicontinuousCauchyFamilyEncodeBHist C))
            (equicontinuousCauchyFamilyDecodeBHist
              (equicontinuousCauchyFamilyEncodeBHist P))
            (equicontinuousCauchyFamilyDecodeBHist
              (equicontinuousCauchyFamilyEncodeBHist N))) =
          some (EquicontinuousCauchyFamilyUp.mk K U M T W R D A H C P N)
      rw [EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_decode_encode K,
        EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_decode_encode U,
        EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_decode_encode M,
        EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_decode_encode T,
        EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_decode_encode W,
        EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_decode_encode R,
        EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_decode_encode D,
        EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_decode_encode A,
        EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_decode_encode H,
        EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_decode_encode C,
        EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_decode_encode P,
        EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_decode_encode N]

private theorem EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_injective
    {x y : EquicontinuousCauchyFamilyUp} :
    equicontinuousCauchyFamilyToEventFlow x =
        equicontinuousCauchyFamilyToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      equicontinuousCauchyFamilyFromEventFlow (equicontinuousCauchyFamilyToEventFlow x) =
        equicontinuousCauchyFamilyFromEventFlow
          (equicontinuousCauchyFamilyToEventFlow y) :=
    congrArg equicontinuousCauchyFamilyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_round_trip y)))

instance equicontinuousCauchyFamilyBHistCarrier :
    BHistCarrier EquicontinuousCauchyFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := equicontinuousCauchyFamilyToEventFlow
  fromEventFlow := equicontinuousCauchyFamilyFromEventFlow

instance equicontinuousCauchyFamilyChapterTasteGate :
    ChapterTasteGate EquicontinuousCauchyFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      equicontinuousCauchyFamilyFromEventFlow
          (equicontinuousCauchyFamilyToEventFlow x) =
        some x
    exact EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate EquicontinuousCauchyFamilyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  equicontinuousCauchyFamilyChapterTasteGate

theorem EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      equicontinuousCauchyFamilyDecodeBHist
          (equicontinuousCauchyFamilyEncodeBHist h) =
        h) ∧
      (∀ x : EquicontinuousCauchyFamilyUp,
        equicontinuousCauchyFamilyFromEventFlow
            (equicontinuousCauchyFamilyToEventFlow x) =
          some x) ∧
        (∀ x y : EquicontinuousCauchyFamilyUp,
          equicontinuousCauchyFamilyToEventFlow x =
              equicontinuousCauchyFamilyToEventFlow y →
            x = y) ∧
          equicontinuousCauchyFamilyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_decode_encode,
      EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        EquicontinuousCauchyFamilyTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.EquicontinuousCauchyFamilyUp
