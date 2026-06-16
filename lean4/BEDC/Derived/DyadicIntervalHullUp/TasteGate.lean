import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicIntervalHullUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicIntervalHullUp : Type where
  | mk (L U O A B S R E T C P N : BHist) : DyadicIntervalHullUp
  deriving DecidableEq

def dyadicIntervalHullEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicIntervalHullEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicIntervalHullEncodeBHist h

def dyadicIntervalHullDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicIntervalHullDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicIntervalHullDecodeBHist tail)

private theorem DyadicIntervalHullTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, dyadicIntervalHullDecodeBHist (dyadicIntervalHullEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicIntervalHullFields : DyadicIntervalHullUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicIntervalHullUp.mk L U O A B S R E T C P N =>
      [L, U, O, A, B, S, R, E, T, C, P, N]

def dyadicIntervalHullToEventFlow : DyadicIntervalHullUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicIntervalHullFields x).map dyadicIntervalHullEncodeBHist

private def dyadicIntervalHullEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicIntervalHullEventAtDefault index rest

def dyadicIntervalHullFromEventFlow (ef : EventFlow) : Option DyadicIntervalHullUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicIntervalHullUp.mk
      (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEventAtDefault 0 ef))
      (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEventAtDefault 1 ef))
      (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEventAtDefault 2 ef))
      (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEventAtDefault 3 ef))
      (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEventAtDefault 4 ef))
      (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEventAtDefault 5 ef))
      (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEventAtDefault 6 ef))
      (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEventAtDefault 7 ef))
      (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEventAtDefault 8 ef))
      (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEventAtDefault 9 ef))
      (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEventAtDefault 10 ef))
      (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEventAtDefault 11 ef)))

private theorem DyadicIntervalHullTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicIntervalHullUp,
      dyadicIntervalHullFromEventFlow (dyadicIntervalHullToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U O A B S R E T C P N =>
      change
        some
          (DyadicIntervalHullUp.mk
            (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEncodeBHist L))
            (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEncodeBHist U))
            (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEncodeBHist O))
            (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEncodeBHist A))
            (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEncodeBHist B))
            (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEncodeBHist S))
            (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEncodeBHist R))
            (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEncodeBHist E))
            (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEncodeBHist T))
            (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEncodeBHist C))
            (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEncodeBHist P))
            (dyadicIntervalHullDecodeBHist (dyadicIntervalHullEncodeBHist N))) =
          some (DyadicIntervalHullUp.mk L U O A B S R E T C P N)
      rw [
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode L,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode U,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode O,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode A,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode B,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode S,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode R,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode E,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode T,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode C,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode P,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode N]

private theorem DyadicIntervalHullTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicIntervalHullUp} :
    dyadicIntervalHullToEventFlow x = dyadicIntervalHullToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicIntervalHullFromEventFlow (dyadicIntervalHullToEventFlow x) =
        dyadicIntervalHullFromEventFlow (dyadicIntervalHullToEventFlow y) :=
    congrArg dyadicIntervalHullFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicIntervalHullTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicIntervalHullTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicIntervalHullTasteGate_single_carrier_alignment_fields :
    ∀ x y : DyadicIntervalHullUp,
      dyadicIntervalHullFields x = dyadicIntervalHullFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 U1 O1 A1 B1 S1 R1 E1 T1 C1 P1 N1 =>
      cases y with
      | mk L2 U2 O2 A2 B2 S2 R2 E2 T2 C2 P2 N2 =>
          cases hfields
          rfl

instance dyadicIntervalHullBHistCarrier : BHistCarrier DyadicIntervalHullUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicIntervalHullToEventFlow
  fromEventFlow := dyadicIntervalHullFromEventFlow

instance dyadicIntervalHullChapterTasteGate : ChapterTasteGate DyadicIntervalHullUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicIntervalHullFromEventFlow (dyadicIntervalHullToEventFlow x) = some x
    exact DyadicIntervalHullTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicIntervalHullTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicIntervalHullFieldFaithful : FieldFaithful DyadicIntervalHullUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicIntervalHullFields
  field_faithful := DyadicIntervalHullTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate DyadicIntervalHullUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicIntervalHullChapterTasteGate

theorem DyadicIntervalHullTasteGate_single_carrier_alignment :
    (dyadicIntervalHullEncodeBHist BHist.Empty = ([] : RawEvent)) ∧
      (∀ h : BHist, dyadicIntervalHullDecodeBHist (dyadicIntervalHullEncodeBHist h) = h) ∧
        (∀ x : DyadicIntervalHullUp,
          dyadicIntervalHullFromEventFlow (dyadicIntervalHullToEventFlow x) = some x) ∧
          (∀ x y : DyadicIntervalHullUp,
            dyadicIntervalHullFields x = dyadicIntervalHullFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨rfl,
      DyadicIntervalHullTasteGate_single_carrier_alignment_decode,
      DyadicIntervalHullTasteGate_single_carrier_alignment_round_trip,
      DyadicIntervalHullTasteGate_single_carrier_alignment_fields⟩

end BEDC.Derived.DyadicIntervalHullUp
