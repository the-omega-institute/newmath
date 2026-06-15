import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicIntervalTreeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicIntervalTreeUp : Type where
  | mk (R D B F M Q NW H C P L : BHist) : DyadicIntervalTreeUp
  deriving DecidableEq

def dyadicIntervalTreeEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicIntervalTreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicIntervalTreeEncodeBHist h

def dyadicIntervalTreeDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicIntervalTreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicIntervalTreeDecodeBHist tail)

theorem DyadicIntervalTreeTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicIntervalTreeFields : DyadicIntervalTreeUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicIntervalTreeUp.mk R D B F M Q NW H C P L => [R, D, B, F, M, Q, NW, H, C, P, L]

def dyadicIntervalTreeToEventFlow : DyadicIntervalTreeUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicIntervalTreeFields x).map dyadicIntervalTreeEncodeBHist

private def dyadicIntervalTreeRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => dyadicIntervalTreeRawAt n rest

private def dyadicIntervalTreeLengthEq : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => dyadicIntervalTreeLengthEq n rest

def dyadicIntervalTreeFromEventFlow : EventFlow -> Option DyadicIntervalTreeUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match dyadicIntervalTreeLengthEq 11 flow with
      | true =>
          some
            (DyadicIntervalTreeUp.mk
              (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeRawAt 0 flow))
              (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeRawAt 1 flow))
              (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeRawAt 2 flow))
              (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeRawAt 3 flow))
              (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeRawAt 4 flow))
              (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeRawAt 5 flow))
              (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeRawAt 6 flow))
              (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeRawAt 7 flow))
              (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeRawAt 8 flow))
              (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeRawAt 9 flow))
              (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeRawAt 10 flow)))
      | false => none

theorem DyadicIntervalTreeTasteGate_single_carrier_alignment_round_trip :
    forall x : DyadicIntervalTreeUp,
      dyadicIntervalTreeFromEventFlow (dyadicIntervalTreeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R D B F M Q NW H C P L =>
      change
        some
          (DyadicIntervalTreeUp.mk
            (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeEncodeBHist R))
            (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeEncodeBHist D))
            (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeEncodeBHist B))
            (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeEncodeBHist F))
            (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeEncodeBHist M))
            (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeEncodeBHist Q))
            (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeEncodeBHist NW))
            (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeEncodeBHist H))
            (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeEncodeBHist C))
            (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeEncodeBHist P))
            (dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeEncodeBHist L))) =
          some (DyadicIntervalTreeUp.mk R D B F M Q NW H C P L)
      rw [DyadicIntervalTreeTasteGate_single_carrier_alignment_decode_encode R,
        DyadicIntervalTreeTasteGate_single_carrier_alignment_decode_encode D,
        DyadicIntervalTreeTasteGate_single_carrier_alignment_decode_encode B,
        DyadicIntervalTreeTasteGate_single_carrier_alignment_decode_encode F,
        DyadicIntervalTreeTasteGate_single_carrier_alignment_decode_encode M,
        DyadicIntervalTreeTasteGate_single_carrier_alignment_decode_encode Q,
        DyadicIntervalTreeTasteGate_single_carrier_alignment_decode_encode NW,
        DyadicIntervalTreeTasteGate_single_carrier_alignment_decode_encode H,
        DyadicIntervalTreeTasteGate_single_carrier_alignment_decode_encode C,
        DyadicIntervalTreeTasteGate_single_carrier_alignment_decode_encode P,
        DyadicIntervalTreeTasteGate_single_carrier_alignment_decode_encode L]

theorem DyadicIntervalTreeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicIntervalTreeUp} :
    dyadicIntervalTreeToEventFlow x = dyadicIntervalTreeToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicIntervalTreeFromEventFlow (dyadicIntervalTreeToEventFlow x) =
        dyadicIntervalTreeFromEventFlow (dyadicIntervalTreeToEventFlow y) :=
    congrArg dyadicIntervalTreeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicIntervalTreeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicIntervalTreeTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicIntervalTreeBHistCarrier : BHistCarrier DyadicIntervalTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicIntervalTreeToEventFlow
  fromEventFlow := dyadicIntervalTreeFromEventFlow

instance dyadicIntervalTreeChapterTasteGate : ChapterTasteGate DyadicIntervalTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicIntervalTreeFromEventFlow (dyadicIntervalTreeToEventFlow x) = some x
    exact DyadicIntervalTreeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicIntervalTreeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DyadicIntervalTreeTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicIntervalTreeDecodeBHist (dyadicIntervalTreeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DyadicIntervalTreeUp) ∧
        Nonempty (ChapterTasteGate DyadicIntervalTreeUp) ∧
          dyadicIntervalTreeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact DyadicIntervalTreeTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨dyadicIntervalTreeBHistCarrier⟩
    · constructor
      · exact ⟨dyadicIntervalTreeChapterTasteGate⟩
      · rfl

end BEDC.Derived.DyadicIntervalTreeUp
