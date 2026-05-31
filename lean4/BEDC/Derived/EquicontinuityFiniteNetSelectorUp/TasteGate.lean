import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EquicontinuityFiniteNetSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EquicontinuityFiniteNetSelectorUp : Type where
  | mk (F K G N R L U H C P A : BHist) : EquicontinuityFiniteNetSelectorUp
  deriving DecidableEq

def equicontinuityFiniteNetSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: equicontinuityFiniteNetSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: equicontinuityFiniteNetSelectorEncodeBHist h

def equicontinuityFiniteNetSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (equicontinuityFiniteNetSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (equicontinuityFiniteNetSelectorDecodeBHist tail)

private theorem EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      equicontinuityFiniteNetSelectorDecodeBHist
        (equicontinuityFiniteNetSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def equicontinuityFiniteNetSelectorFields :
    EquicontinuityFiniteNetSelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EquicontinuityFiniteNetSelectorUp.mk F K G N R L U H C P A =>
      [F, K, G, N, R, L, U, H, C, P, A]

def equicontinuityFiniteNetSelectorToEventFlow :
    EquicontinuityFiniteNetSelectorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (equicontinuityFiniteNetSelectorFields x).map
      equicontinuityFiniteNetSelectorEncodeBHist

private def equicontinuityFiniteNetSelectorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      equicontinuityFiniteNetSelectorEventAtDefault index rest

def equicontinuityFiniteNetSelectorFromEventFlow
    (ef : EventFlow) : Option EquicontinuityFiniteNetSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EquicontinuityFiniteNetSelectorUp.mk
      (equicontinuityFiniteNetSelectorDecodeBHist
        (equicontinuityFiniteNetSelectorEventAtDefault 0 ef))
      (equicontinuityFiniteNetSelectorDecodeBHist
        (equicontinuityFiniteNetSelectorEventAtDefault 1 ef))
      (equicontinuityFiniteNetSelectorDecodeBHist
        (equicontinuityFiniteNetSelectorEventAtDefault 2 ef))
      (equicontinuityFiniteNetSelectorDecodeBHist
        (equicontinuityFiniteNetSelectorEventAtDefault 3 ef))
      (equicontinuityFiniteNetSelectorDecodeBHist
        (equicontinuityFiniteNetSelectorEventAtDefault 4 ef))
      (equicontinuityFiniteNetSelectorDecodeBHist
        (equicontinuityFiniteNetSelectorEventAtDefault 5 ef))
      (equicontinuityFiniteNetSelectorDecodeBHist
        (equicontinuityFiniteNetSelectorEventAtDefault 6 ef))
      (equicontinuityFiniteNetSelectorDecodeBHist
        (equicontinuityFiniteNetSelectorEventAtDefault 7 ef))
      (equicontinuityFiniteNetSelectorDecodeBHist
        (equicontinuityFiniteNetSelectorEventAtDefault 8 ef))
      (equicontinuityFiniteNetSelectorDecodeBHist
        (equicontinuityFiniteNetSelectorEventAtDefault 9 ef))
      (equicontinuityFiniteNetSelectorDecodeBHist
        (equicontinuityFiniteNetSelectorEventAtDefault 10 ef)))

private theorem EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EquicontinuityFiniteNetSelectorUp,
      equicontinuityFiniteNetSelectorFromEventFlow
        (equicontinuityFiniteNetSelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F K G N R L U H C P A =>
      change
        some
            (EquicontinuityFiniteNetSelectorUp.mk
              (equicontinuityFiniteNetSelectorDecodeBHist
                (equicontinuityFiniteNetSelectorEncodeBHist F))
              (equicontinuityFiniteNetSelectorDecodeBHist
                (equicontinuityFiniteNetSelectorEncodeBHist K))
              (equicontinuityFiniteNetSelectorDecodeBHist
                (equicontinuityFiniteNetSelectorEncodeBHist G))
              (equicontinuityFiniteNetSelectorDecodeBHist
                (equicontinuityFiniteNetSelectorEncodeBHist N))
              (equicontinuityFiniteNetSelectorDecodeBHist
                (equicontinuityFiniteNetSelectorEncodeBHist R))
              (equicontinuityFiniteNetSelectorDecodeBHist
                (equicontinuityFiniteNetSelectorEncodeBHist L))
              (equicontinuityFiniteNetSelectorDecodeBHist
                (equicontinuityFiniteNetSelectorEncodeBHist U))
              (equicontinuityFiniteNetSelectorDecodeBHist
                (equicontinuityFiniteNetSelectorEncodeBHist H))
              (equicontinuityFiniteNetSelectorDecodeBHist
                (equicontinuityFiniteNetSelectorEncodeBHist C))
              (equicontinuityFiniteNetSelectorDecodeBHist
                (equicontinuityFiniteNetSelectorEncodeBHist P))
              (equicontinuityFiniteNetSelectorDecodeBHist
                (equicontinuityFiniteNetSelectorEncodeBHist A))) =
          some (EquicontinuityFiniteNetSelectorUp.mk F K G N R L U H C P A)
      rw [EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_decode F,
        EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_decode K,
        EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_decode G,
        EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_decode N,
        EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_decode R,
        EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_decode L,
        EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_decode U,
        EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_decode H,
        EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_decode C,
        EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_decode P,
        EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_decode A]

private theorem EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EquicontinuityFiniteNetSelectorUp} :
    equicontinuityFiniteNetSelectorToEventFlow x =
        equicontinuityFiniteNetSelectorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      equicontinuityFiniteNetSelectorFromEventFlow
          (equicontinuityFiniteNetSelectorToEventFlow x) =
        equicontinuityFiniteNetSelectorFromEventFlow
          (equicontinuityFiniteNetSelectorToEventFlow y) :=
    congrArg equicontinuityFiniteNetSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_round_trip y)))

instance equicontinuityFiniteNetSelectorBHistCarrier :
    BHistCarrier EquicontinuityFiniteNetSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := equicontinuityFiniteNetSelectorToEventFlow
  fromEventFlow := equicontinuityFiniteNetSelectorFromEventFlow

instance equicontinuityFiniteNetSelectorChapterTasteGate :
    ChapterTasteGate EquicontinuityFiniteNetSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      equicontinuityFiniteNetSelectorFromEventFlow
        (equicontinuityFiniteNetSelectorToEventFlow x) = some x
    exact EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      equicontinuityFiniteNetSelectorDecodeBHist
        (equicontinuityFiniteNetSelectorEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier EquicontinuityFiniteNetSelectorUp) ∧
        Nonempty (ChapterTasteGate EquicontinuityFiniteNetSelectorUp) ∧
          equicontinuityFiniteNetSelectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨EquicontinuityFiniteNetSelectorTasteGate_single_carrier_alignment_decode,
      ⟨equicontinuityFiniteNetSelectorBHistCarrier⟩,
      ⟨equicontinuityFiniteNetSelectorChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.EquicontinuityFiniteNetSelectorUp
