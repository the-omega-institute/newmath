import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedApartnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedApartnessUp : Type where
  | mk (L0 L1 S R0 R1 D G A H C P N : BHist) : LocatedApartnessUp
  deriving DecidableEq

def locatedApartnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedApartnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedApartnessEncodeBHist h

def locatedApartnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedApartnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedApartnessDecodeBHist tail)

private theorem LocatedApartnessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, locatedApartnessDecodeBHist (locatedApartnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedApartnessFields : LocatedApartnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedApartnessUp.mk L0 L1 S R0 R1 D G A H C P N =>
      [L0, L1, S, R0, R1, D, G, A, H, C, P, N]

def locatedApartnessToEventFlow : LocatedApartnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map locatedApartnessEncodeBHist (locatedApartnessFields x)

private def locatedApartnessEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedApartnessEventAt index rest

def locatedApartnessFromEventFlow : EventFlow → Option LocatedApartnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (LocatedApartnessUp.mk
          (locatedApartnessDecodeBHist (locatedApartnessEventAt 0 ef))
          (locatedApartnessDecodeBHist (locatedApartnessEventAt 1 ef))
          (locatedApartnessDecodeBHist (locatedApartnessEventAt 2 ef))
          (locatedApartnessDecodeBHist (locatedApartnessEventAt 3 ef))
          (locatedApartnessDecodeBHist (locatedApartnessEventAt 4 ef))
          (locatedApartnessDecodeBHist (locatedApartnessEventAt 5 ef))
          (locatedApartnessDecodeBHist (locatedApartnessEventAt 6 ef))
          (locatedApartnessDecodeBHist (locatedApartnessEventAt 7 ef))
          (locatedApartnessDecodeBHist (locatedApartnessEventAt 8 ef))
          (locatedApartnessDecodeBHist (locatedApartnessEventAt 9 ef))
          (locatedApartnessDecodeBHist (locatedApartnessEventAt 10 ef))
          (locatedApartnessDecodeBHist (locatedApartnessEventAt 11 ef)))

private theorem LocatedApartnessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedApartnessUp,
      locatedApartnessFromEventFlow (locatedApartnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L0 L1 S R0 R1 D G A H C P N =>
      change
        some
          (LocatedApartnessUp.mk
            (locatedApartnessDecodeBHist (locatedApartnessEncodeBHist L0))
            (locatedApartnessDecodeBHist (locatedApartnessEncodeBHist L1))
            (locatedApartnessDecodeBHist (locatedApartnessEncodeBHist S))
            (locatedApartnessDecodeBHist (locatedApartnessEncodeBHist R0))
            (locatedApartnessDecodeBHist (locatedApartnessEncodeBHist R1))
            (locatedApartnessDecodeBHist (locatedApartnessEncodeBHist D))
            (locatedApartnessDecodeBHist (locatedApartnessEncodeBHist G))
            (locatedApartnessDecodeBHist (locatedApartnessEncodeBHist A))
            (locatedApartnessDecodeBHist (locatedApartnessEncodeBHist H))
            (locatedApartnessDecodeBHist (locatedApartnessEncodeBHist C))
            (locatedApartnessDecodeBHist (locatedApartnessEncodeBHist P))
            (locatedApartnessDecodeBHist (locatedApartnessEncodeBHist N))) =
          some (LocatedApartnessUp.mk L0 L1 S R0 R1 D G A H C P N)
      rw [LocatedApartnessTasteGate_single_carrier_alignment_decode L0,
        LocatedApartnessTasteGate_single_carrier_alignment_decode L1,
        LocatedApartnessTasteGate_single_carrier_alignment_decode S,
        LocatedApartnessTasteGate_single_carrier_alignment_decode R0,
        LocatedApartnessTasteGate_single_carrier_alignment_decode R1,
        LocatedApartnessTasteGate_single_carrier_alignment_decode D,
        LocatedApartnessTasteGate_single_carrier_alignment_decode G,
        LocatedApartnessTasteGate_single_carrier_alignment_decode A,
        LocatedApartnessTasteGate_single_carrier_alignment_decode H,
        LocatedApartnessTasteGate_single_carrier_alignment_decode C,
        LocatedApartnessTasteGate_single_carrier_alignment_decode P,
        LocatedApartnessTasteGate_single_carrier_alignment_decode N]

private theorem LocatedApartnessTasteGate_single_carrier_alignment_injective
    {x y : LocatedApartnessUp} :
    locatedApartnessToEventFlow x = locatedApartnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedApartnessFromEventFlow (locatedApartnessToEventFlow x) =
        locatedApartnessFromEventFlow (locatedApartnessToEventFlow y) :=
    congrArg locatedApartnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedApartnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedApartnessTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedApartnessTasteGate_single_carrier_alignment_fields :
    ∀ x y : LocatedApartnessUp, locatedApartnessFields x = locatedApartnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L01 L11 S1 R01 R11 D1 G1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk L02 L12 S2 R02 R12 D2 G2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance locatedApartnessBHistCarrier : BHistCarrier LocatedApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedApartnessToEventFlow
  fromEventFlow := locatedApartnessFromEventFlow

instance locatedApartnessChapterTasteGate : ChapterTasteGate LocatedApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedApartnessFromEventFlow (locatedApartnessToEventFlow x) = some x
    exact LocatedApartnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedApartnessTasteGate_single_carrier_alignment_injective heq)

theorem LocatedApartnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedApartnessDecodeBHist (locatedApartnessEncodeBHist h) = h) ∧
      (∀ x : LocatedApartnessUp,
        locatedApartnessFromEventFlow (locatedApartnessToEventFlow x) = some x) ∧
        (∀ x y : LocatedApartnessUp,
          locatedApartnessToEventFlow x = locatedApartnessToEventFlow y → x = y) ∧
          locatedApartnessEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : LocatedApartnessUp, locatedApartnessFields x = locatedApartnessFields y →
              x = y) ∧
              (∃ x y : LocatedApartnessUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact LocatedApartnessTasteGate_single_carrier_alignment_decode
  · constructor
    · exact LocatedApartnessTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact LocatedApartnessTasteGate_single_carrier_alignment_injective heq
      · constructor
        · rfl
        · constructor
          · exact LocatedApartnessTasteGate_single_carrier_alignment_fields
          · exact
              Exists.intro
                (LocatedApartnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty)
                (Exists.intro
                  (LocatedApartnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty)
                  (by
                    intro h
                    cases h))

end BEDC.Derived.LocatedApartnessUp
