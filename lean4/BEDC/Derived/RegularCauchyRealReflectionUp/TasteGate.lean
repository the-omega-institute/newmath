import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyRealReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyRealReflectionUp : Type where
  | mk (G S E D R H C P N : BHist) : RegularCauchyRealReflectionUp

def regularCauchyRealReflectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyRealReflectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyRealReflectionEncodeBHist h

def regularCauchyRealReflectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyRealReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyRealReflectionDecodeBHist tail)

private theorem RegularCauchyRealReflectionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyRealReflectionDecodeBHist
          (regularCauchyRealReflectionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyRealReflectionFields :
    RegularCauchyRealReflectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyRealReflectionUp.mk G S E D R H C P N => [G, S, E, D, R, H, C, P, N]

def regularCauchyRealReflectionToEventFlow :
    RegularCauchyRealReflectionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchyRealReflectionFields x).map regularCauchyRealReflectionEncodeBHist

private def regularCauchyRealReflectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyRealReflectionEventAtDefault index rest

def regularCauchyRealReflectionFromEventFlow
    (ef : EventFlow) : Option RegularCauchyRealReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyRealReflectionUp.mk
      (regularCauchyRealReflectionDecodeBHist
        (regularCauchyRealReflectionEventAtDefault 0 ef))
      (regularCauchyRealReflectionDecodeBHist
        (regularCauchyRealReflectionEventAtDefault 1 ef))
      (regularCauchyRealReflectionDecodeBHist
        (regularCauchyRealReflectionEventAtDefault 2 ef))
      (regularCauchyRealReflectionDecodeBHist
        (regularCauchyRealReflectionEventAtDefault 3 ef))
      (regularCauchyRealReflectionDecodeBHist
        (regularCauchyRealReflectionEventAtDefault 4 ef))
      (regularCauchyRealReflectionDecodeBHist
        (regularCauchyRealReflectionEventAtDefault 5 ef))
      (regularCauchyRealReflectionDecodeBHist
        (regularCauchyRealReflectionEventAtDefault 6 ef))
      (regularCauchyRealReflectionDecodeBHist
        (regularCauchyRealReflectionEventAtDefault 7 ef))
      (regularCauchyRealReflectionDecodeBHist
        (regularCauchyRealReflectionEventAtDefault 8 ef)))

private theorem RegularCauchyRealReflectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyRealReflectionUp,
      regularCauchyRealReflectionFromEventFlow
          (regularCauchyRealReflectionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G S E D R H C P N =>
      change
        some
          (RegularCauchyRealReflectionUp.mk
            (regularCauchyRealReflectionDecodeBHist
              (regularCauchyRealReflectionEncodeBHist G))
            (regularCauchyRealReflectionDecodeBHist
              (regularCauchyRealReflectionEncodeBHist S))
            (regularCauchyRealReflectionDecodeBHist
              (regularCauchyRealReflectionEncodeBHist E))
            (regularCauchyRealReflectionDecodeBHist
              (regularCauchyRealReflectionEncodeBHist D))
            (regularCauchyRealReflectionDecodeBHist
              (regularCauchyRealReflectionEncodeBHist R))
            (regularCauchyRealReflectionDecodeBHist
              (regularCauchyRealReflectionEncodeBHist H))
            (regularCauchyRealReflectionDecodeBHist
              (regularCauchyRealReflectionEncodeBHist C))
            (regularCauchyRealReflectionDecodeBHist
              (regularCauchyRealReflectionEncodeBHist P))
            (regularCauchyRealReflectionDecodeBHist
              (regularCauchyRealReflectionEncodeBHist N))) =
          some (RegularCauchyRealReflectionUp.mk G S E D R H C P N)
      rw [RegularCauchyRealReflectionTasteGate_single_carrier_alignment_decode G,
        RegularCauchyRealReflectionTasteGate_single_carrier_alignment_decode S,
        RegularCauchyRealReflectionTasteGate_single_carrier_alignment_decode E,
        RegularCauchyRealReflectionTasteGate_single_carrier_alignment_decode D,
        RegularCauchyRealReflectionTasteGate_single_carrier_alignment_decode R,
        RegularCauchyRealReflectionTasteGate_single_carrier_alignment_decode H,
        RegularCauchyRealReflectionTasteGate_single_carrier_alignment_decode C,
        RegularCauchyRealReflectionTasteGate_single_carrier_alignment_decode P,
        RegularCauchyRealReflectionTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyRealReflectionTasteGate_single_carrier_alignment_injective
    {x y : RegularCauchyRealReflectionUp} :
    regularCauchyRealReflectionToEventFlow x =
        regularCauchyRealReflectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyRealReflectionFromEventFlow
          (regularCauchyRealReflectionToEventFlow x) =
        regularCauchyRealReflectionFromEventFlow
          (regularCauchyRealReflectionToEventFlow y) :=
    congrArg regularCauchyRealReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyRealReflectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyRealReflectionTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyRealReflectionBHistCarrier :
    BHistCarrier RegularCauchyRealReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyRealReflectionToEventFlow
  fromEventFlow := regularCauchyRealReflectionFromEventFlow

instance regularCauchyRealReflectionChapterTasteGate :
    ChapterTasteGate RegularCauchyRealReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyRealReflectionFromEventFlow
          (regularCauchyRealReflectionToEventFlow x) =
        some x
    exact RegularCauchyRealReflectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyRealReflectionTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyRealReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyRealReflectionChapterTasteGate

theorem RegularCauchyRealReflectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyRealReflectionDecodeBHist (regularCauchyRealReflectionEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier RegularCauchyRealReflectionUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyRealReflectionUp) ∧
          regularCauchyRealReflectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyRealReflectionTasteGate_single_carrier_alignment_decode,
      ⟨⟨regularCauchyRealReflectionBHistCarrier⟩,
        ⟨⟨regularCauchyRealReflectionChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.RegularCauchyRealReflectionUp
