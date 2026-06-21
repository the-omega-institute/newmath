import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicGridProjectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicGridProjectionUp : Type where
  | mk (x n a b I E H C P N : BHist) : DyadicGridProjectionUp
  deriving DecidableEq

def dyadicGridProjectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicGridProjectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicGridProjectionEncodeBHist h

def dyadicGridProjectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicGridProjectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicGridProjectionDecodeBHist tail)

private theorem DyadicGridProjectionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      dyadicGridProjectionDecodeBHist (dyadicGridProjectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicGridProjectionFields : DyadicGridProjectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicGridProjectionUp.mk x n a b I E H C P N => [x, n, a, b, I, E, H, C, P, N]

def dyadicGridProjectionToEventFlow : DyadicGridProjectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicGridProjectionFields x).map dyadicGridProjectionEncodeBHist

private def DyadicGridProjectionTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      DyadicGridProjectionTasteGate_single_carrier_alignment_eventAt index rest

def dyadicGridProjectionFromEventFlow (ef : EventFlow) :
    Option DyadicGridProjectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicGridProjectionUp.mk
      (dyadicGridProjectionDecodeBHist
        (DyadicGridProjectionTasteGate_single_carrier_alignment_eventAt 0 ef))
      (dyadicGridProjectionDecodeBHist
        (DyadicGridProjectionTasteGate_single_carrier_alignment_eventAt 1 ef))
      (dyadicGridProjectionDecodeBHist
        (DyadicGridProjectionTasteGate_single_carrier_alignment_eventAt 2 ef))
      (dyadicGridProjectionDecodeBHist
        (DyadicGridProjectionTasteGate_single_carrier_alignment_eventAt 3 ef))
      (dyadicGridProjectionDecodeBHist
        (DyadicGridProjectionTasteGate_single_carrier_alignment_eventAt 4 ef))
      (dyadicGridProjectionDecodeBHist
        (DyadicGridProjectionTasteGate_single_carrier_alignment_eventAt 5 ef))
      (dyadicGridProjectionDecodeBHist
        (DyadicGridProjectionTasteGate_single_carrier_alignment_eventAt 6 ef))
      (dyadicGridProjectionDecodeBHist
        (DyadicGridProjectionTasteGate_single_carrier_alignment_eventAt 7 ef))
      (dyadicGridProjectionDecodeBHist
        (DyadicGridProjectionTasteGate_single_carrier_alignment_eventAt 8 ef))
      (dyadicGridProjectionDecodeBHist
        (DyadicGridProjectionTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem DyadicGridProjectionTasteGate_single_carrier_alignment_round_trip
    (carrier : DyadicGridProjectionUp) :
    dyadicGridProjectionFromEventFlow (dyadicGridProjectionToEventFlow carrier) =
      some carrier := by
  -- BEDC touchpoint anchor: BHist BMark
  cases carrier with
  | mk x n a b I E H C P N =>
      change
        some
          (DyadicGridProjectionUp.mk
            (dyadicGridProjectionDecodeBHist (dyadicGridProjectionEncodeBHist x))
            (dyadicGridProjectionDecodeBHist (dyadicGridProjectionEncodeBHist n))
            (dyadicGridProjectionDecodeBHist (dyadicGridProjectionEncodeBHist a))
            (dyadicGridProjectionDecodeBHist (dyadicGridProjectionEncodeBHist b))
            (dyadicGridProjectionDecodeBHist (dyadicGridProjectionEncodeBHist I))
            (dyadicGridProjectionDecodeBHist (dyadicGridProjectionEncodeBHist E))
            (dyadicGridProjectionDecodeBHist (dyadicGridProjectionEncodeBHist H))
            (dyadicGridProjectionDecodeBHist (dyadicGridProjectionEncodeBHist C))
            (dyadicGridProjectionDecodeBHist (dyadicGridProjectionEncodeBHist P))
            (dyadicGridProjectionDecodeBHist (dyadicGridProjectionEncodeBHist N))) =
          some (DyadicGridProjectionUp.mk x n a b I E H C P N)
      rw [DyadicGridProjectionTasteGate_single_carrier_alignment_decode_encode x,
        DyadicGridProjectionTasteGate_single_carrier_alignment_decode_encode n,
        DyadicGridProjectionTasteGate_single_carrier_alignment_decode_encode a,
        DyadicGridProjectionTasteGate_single_carrier_alignment_decode_encode b,
        DyadicGridProjectionTasteGate_single_carrier_alignment_decode_encode I,
        DyadicGridProjectionTasteGate_single_carrier_alignment_decode_encode E,
        DyadicGridProjectionTasteGate_single_carrier_alignment_decode_encode H,
        DyadicGridProjectionTasteGate_single_carrier_alignment_decode_encode C,
        DyadicGridProjectionTasteGate_single_carrier_alignment_decode_encode P,
        DyadicGridProjectionTasteGate_single_carrier_alignment_decode_encode N]

private theorem DyadicGridProjectionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicGridProjectionUp} :
    dyadicGridProjectionToEventFlow x = dyadicGridProjectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicGridProjectionFromEventFlow (dyadicGridProjectionToEventFlow x) =
        dyadicGridProjectionFromEventFlow (dyadicGridProjectionToEventFlow y) :=
    congrArg dyadicGridProjectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicGridProjectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicGridProjectionTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicGridProjectionBHistCarrier : BHistCarrier DyadicGridProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicGridProjectionToEventFlow
  fromEventFlow := dyadicGridProjectionFromEventFlow

instance dyadicGridProjectionChapterTasteGate :
    ChapterTasteGate DyadicGridProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicGridProjectionFromEventFlow (dyadicGridProjectionToEventFlow x) = some x
    exact DyadicGridProjectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicGridProjectionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DyadicGridProjectionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier DyadicGridProjectionUp) ∧
      Nonempty (ChapterTasteGate DyadicGridProjectionUp) ∧
        dyadicGridProjectionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨dyadicGridProjectionBHistCarrier⟩, ⟨dyadicGridProjectionChapterTasteGate⟩, rfl⟩

end BEDC.Derived.DyadicGridProjectionUp
