import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedSupremumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedSupremumUp : Type where
  | mk (L U A W R E H C P N : BHist) : LocatedSupremumUp
  deriving DecidableEq

def locatedSupremumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedSupremumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedSupremumEncodeBHist h

def locatedSupremumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedSupremumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedSupremumDecodeBHist tail)

private theorem LocatedSupremumTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, locatedSupremumDecodeBHist (locatedSupremumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedSupremumFields : LocatedSupremumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedSupremumUp.mk L U A W R E H C P N => [L, U, A, W, R, E, H, C, P, N]

def locatedSupremumToEventFlow : LocatedSupremumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map locatedSupremumEncodeBHist (locatedSupremumFields x)

private def locatedSupremumEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedSupremumEventAt index rest

def locatedSupremumFromEventFlow : EventFlow → Option LocatedSupremumUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (LocatedSupremumUp.mk
          (locatedSupremumDecodeBHist (locatedSupremumEventAt 0 ef))
          (locatedSupremumDecodeBHist (locatedSupremumEventAt 1 ef))
          (locatedSupremumDecodeBHist (locatedSupremumEventAt 2 ef))
          (locatedSupremumDecodeBHist (locatedSupremumEventAt 3 ef))
          (locatedSupremumDecodeBHist (locatedSupremumEventAt 4 ef))
          (locatedSupremumDecodeBHist (locatedSupremumEventAt 5 ef))
          (locatedSupremumDecodeBHist (locatedSupremumEventAt 6 ef))
          (locatedSupremumDecodeBHist (locatedSupremumEventAt 7 ef))
          (locatedSupremumDecodeBHist (locatedSupremumEventAt 8 ef))
          (locatedSupremumDecodeBHist (locatedSupremumEventAt 9 ef)))

private theorem LocatedSupremumTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedSupremumUp,
      locatedSupremumFromEventFlow (locatedSupremumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U A W R E H C P N =>
      change
        some
          (LocatedSupremumUp.mk
            (locatedSupremumDecodeBHist (locatedSupremumEncodeBHist L))
            (locatedSupremumDecodeBHist (locatedSupremumEncodeBHist U))
            (locatedSupremumDecodeBHist (locatedSupremumEncodeBHist A))
            (locatedSupremumDecodeBHist (locatedSupremumEncodeBHist W))
            (locatedSupremumDecodeBHist (locatedSupremumEncodeBHist R))
            (locatedSupremumDecodeBHist (locatedSupremumEncodeBHist E))
            (locatedSupremumDecodeBHist (locatedSupremumEncodeBHist H))
            (locatedSupremumDecodeBHist (locatedSupremumEncodeBHist C))
            (locatedSupremumDecodeBHist (locatedSupremumEncodeBHist P))
            (locatedSupremumDecodeBHist (locatedSupremumEncodeBHist N))) =
          some (LocatedSupremumUp.mk L U A W R E H C P N)
      rw [LocatedSupremumTasteGate_single_carrier_alignment_decode L,
        LocatedSupremumTasteGate_single_carrier_alignment_decode U,
        LocatedSupremumTasteGate_single_carrier_alignment_decode A,
        LocatedSupremumTasteGate_single_carrier_alignment_decode W,
        LocatedSupremumTasteGate_single_carrier_alignment_decode R,
        LocatedSupremumTasteGate_single_carrier_alignment_decode E,
        LocatedSupremumTasteGate_single_carrier_alignment_decode H,
        LocatedSupremumTasteGate_single_carrier_alignment_decode C,
        LocatedSupremumTasteGate_single_carrier_alignment_decode P,
        LocatedSupremumTasteGate_single_carrier_alignment_decode N]

private theorem LocatedSupremumTasteGate_single_carrier_alignment_injective
    {x y : LocatedSupremumUp} :
    locatedSupremumToEventFlow x = locatedSupremumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedSupremumFromEventFlow (locatedSupremumToEventFlow x) =
        locatedSupremumFromEventFlow (locatedSupremumToEventFlow y) :=
    congrArg locatedSupremumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedSupremumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedSupremumTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedSupremumTasteGate_single_carrier_alignment_fields :
    ∀ x y : LocatedSupremumUp, locatedSupremumFields x = locatedSupremumFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 U1 A1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 U2 A2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance locatedSupremumBHistCarrier : BHistCarrier LocatedSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedSupremumToEventFlow
  fromEventFlow := locatedSupremumFromEventFlow

instance locatedSupremumChapterTasteGate : ChapterTasteGate LocatedSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedSupremumFromEventFlow (locatedSupremumToEventFlow x) = some x
    exact LocatedSupremumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedSupremumTasteGate_single_carrier_alignment_injective heq)

theorem LocatedSupremumTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedSupremumDecodeBHist (locatedSupremumEncodeBHist h) = h) ∧
      (∀ x : LocatedSupremumUp,
        locatedSupremumFromEventFlow (locatedSupremumToEventFlow x) = some x) ∧
        (∀ x y : LocatedSupremumUp,
          locatedSupremumToEventFlow x = locatedSupremumToEventFlow y → x = y) ∧
          locatedSupremumEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : LocatedSupremumUp, locatedSupremumFields x = locatedSupremumFields y →
              x = y) ∧
              (∃ x y : LocatedSupremumUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact LocatedSupremumTasteGate_single_carrier_alignment_decode
  · constructor
    · exact LocatedSupremumTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact LocatedSupremumTasteGate_single_carrier_alignment_injective heq
      · constructor
        · rfl
        · constructor
          · exact LocatedSupremumTasteGate_single_carrier_alignment_fields
          · exact
              Exists.intro
                (LocatedSupremumUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
                (Exists.intro
                  (LocatedSupremumUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty)
                  (by
                    intro h
                    cases h))

end BEDC.Derived.LocatedSupremumUp
