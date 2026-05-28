import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyHausdorffReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

structure RegularCauchyHausdorffReflectionUp where
  leftName : BHist
  rightName : BHist
  leftWindow : BHist
  rightWindow : BHist
  toleranceLedger : BHist
  uniquenessRow : BHist
  realSeal : BHist
  transportRow : BHist
  replayRow : BHist
  provenanceRow : BHist
  localNameCert : BHist

def regularCauchyHausdorffReflectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyHausdorffReflectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyHausdorffReflectionEncodeBHist h

def regularCauchyHausdorffReflectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyHausdorffReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyHausdorffReflectionDecodeBHist tail)

private theorem RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyHausdorffReflectionDecodeBHist
          (regularCauchyHausdorffReflectionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyHausdorffReflectionFields :
    RegularCauchyHausdorffReflectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyHausdorffReflectionUp.mk X Y S T D U E H C P N =>
      [X, Y, S, T, D, U, E, H, C, P, N]

def regularCauchyHausdorffReflectionToEventFlow :
    RegularCauchyHausdorffReflectionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchyHausdorffReflectionFields x).map
      regularCauchyHausdorffReflectionEncodeBHist

private def regularCauchyHausdorffReflectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyHausdorffReflectionEventAtDefault index rest

def regularCauchyHausdorffReflectionFromEventFlow
    (ef : EventFlow) : Option RegularCauchyHausdorffReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyHausdorffReflectionUp.mk
      (regularCauchyHausdorffReflectionDecodeBHist
        (regularCauchyHausdorffReflectionEventAtDefault 0 ef))
      (regularCauchyHausdorffReflectionDecodeBHist
        (regularCauchyHausdorffReflectionEventAtDefault 1 ef))
      (regularCauchyHausdorffReflectionDecodeBHist
        (regularCauchyHausdorffReflectionEventAtDefault 2 ef))
      (regularCauchyHausdorffReflectionDecodeBHist
        (regularCauchyHausdorffReflectionEventAtDefault 3 ef))
      (regularCauchyHausdorffReflectionDecodeBHist
        (regularCauchyHausdorffReflectionEventAtDefault 4 ef))
      (regularCauchyHausdorffReflectionDecodeBHist
        (regularCauchyHausdorffReflectionEventAtDefault 5 ef))
      (regularCauchyHausdorffReflectionDecodeBHist
        (regularCauchyHausdorffReflectionEventAtDefault 6 ef))
      (regularCauchyHausdorffReflectionDecodeBHist
        (regularCauchyHausdorffReflectionEventAtDefault 7 ef))
      (regularCauchyHausdorffReflectionDecodeBHist
        (regularCauchyHausdorffReflectionEventAtDefault 8 ef))
      (regularCauchyHausdorffReflectionDecodeBHist
        (regularCauchyHausdorffReflectionEventAtDefault 9 ef))
      (regularCauchyHausdorffReflectionDecodeBHist
        (regularCauchyHausdorffReflectionEventAtDefault 10 ef)))

private theorem RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyHausdorffReflectionUp,
      regularCauchyHausdorffReflectionFromEventFlow
          (regularCauchyHausdorffReflectionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y S T D U E H C P N =>
      change
        some
          (RegularCauchyHausdorffReflectionUp.mk
            (regularCauchyHausdorffReflectionDecodeBHist
              (regularCauchyHausdorffReflectionEncodeBHist X))
            (regularCauchyHausdorffReflectionDecodeBHist
              (regularCauchyHausdorffReflectionEncodeBHist Y))
            (regularCauchyHausdorffReflectionDecodeBHist
              (regularCauchyHausdorffReflectionEncodeBHist S))
            (regularCauchyHausdorffReflectionDecodeBHist
              (regularCauchyHausdorffReflectionEncodeBHist T))
            (regularCauchyHausdorffReflectionDecodeBHist
              (regularCauchyHausdorffReflectionEncodeBHist D))
            (regularCauchyHausdorffReflectionDecodeBHist
              (regularCauchyHausdorffReflectionEncodeBHist U))
            (regularCauchyHausdorffReflectionDecodeBHist
              (regularCauchyHausdorffReflectionEncodeBHist E))
            (regularCauchyHausdorffReflectionDecodeBHist
              (regularCauchyHausdorffReflectionEncodeBHist H))
            (regularCauchyHausdorffReflectionDecodeBHist
              (regularCauchyHausdorffReflectionEncodeBHist C))
            (regularCauchyHausdorffReflectionDecodeBHist
              (regularCauchyHausdorffReflectionEncodeBHist P))
            (regularCauchyHausdorffReflectionDecodeBHist
              (regularCauchyHausdorffReflectionEncodeBHist N))) =
          some (RegularCauchyHausdorffReflectionUp.mk X Y S T D U E H C P N)
      rw [RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_decode X,
        RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_decode Y,
        RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_decode S,
        RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_decode T,
        RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_decode D,
        RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_decode U,
        RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_decode E,
        RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_decode H,
        RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_decode C,
        RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_decode P,
        RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_injective
    {x y : RegularCauchyHausdorffReflectionUp} :
    regularCauchyHausdorffReflectionToEventFlow x =
        regularCauchyHausdorffReflectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyHausdorffReflectionFromEventFlow
          (regularCauchyHausdorffReflectionToEventFlow x) =
        regularCauchyHausdorffReflectionFromEventFlow
          (regularCauchyHausdorffReflectionToEventFlow y) :=
    congrArg regularCauchyHausdorffReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyHausdorffReflectionBHistCarrier :
    BHistCarrier RegularCauchyHausdorffReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyHausdorffReflectionToEventFlow
  fromEventFlow := regularCauchyHausdorffReflectionFromEventFlow

instance regularCauchyHausdorffReflectionChapterTasteGate :
    ChapterTasteGate RegularCauchyHausdorffReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyHausdorffReflectionFromEventFlow
          (regularCauchyHausdorffReflectionToEventFlow x) =
        some x
    exact RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyHausdorffReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyHausdorffReflectionChapterTasteGate

theorem RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyHausdorffReflectionDecodeBHist
          (regularCauchyHausdorffReflectionEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier RegularCauchyHausdorffReflectionUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyHausdorffReflectionUp) ∧
          regularCauchyHausdorffReflectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment_decode,
      ⟨⟨regularCauchyHausdorffReflectionBHistCarrier⟩,
        ⟨⟨regularCauchyHausdorffReflectionChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.RegularCauchyHausdorffReflectionUp
