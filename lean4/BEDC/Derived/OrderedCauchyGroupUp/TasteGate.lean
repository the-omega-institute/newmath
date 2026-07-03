import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OrderedCauchyGroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OrderedCauchyGroupUp : Type where
  | mk (A O M S R F L E H C P N : BHist) : OrderedCauchyGroupUp
  deriving DecidableEq

def orderedCauchyGroupEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: orderedCauchyGroupEncodeBHist h
  | BHist.e1 h => BMark.b1 :: orderedCauchyGroupEncodeBHist h

def orderedCauchyGroupDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (orderedCauchyGroupDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (orderedCauchyGroupDecodeBHist tail)

private theorem OrderedCauchyGroupTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, orderedCauchyGroupDecodeBHist (orderedCauchyGroupEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def orderedCauchyGroupFields : OrderedCauchyGroupUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OrderedCauchyGroupUp.mk A O M S R F L E H C P N => [A, O, M, S, R, F, L, E, H, C, P, N]

def orderedCauchyGroupToEventFlow : OrderedCauchyGroupUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (orderedCauchyGroupFields x).map orderedCauchyGroupEncodeBHist

private def orderedCauchyGroupEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => orderedCauchyGroupEventAtDefault index rest

def orderedCauchyGroupFromEventFlow (ef : EventFlow) : Option OrderedCauchyGroupUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (OrderedCauchyGroupUp.mk
      (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEventAtDefault 0 ef))
      (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEventAtDefault 1 ef))
      (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEventAtDefault 2 ef))
      (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEventAtDefault 3 ef))
      (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEventAtDefault 4 ef))
      (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEventAtDefault 5 ef))
      (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEventAtDefault 6 ef))
      (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEventAtDefault 7 ef))
      (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEventAtDefault 8 ef))
      (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEventAtDefault 9 ef))
      (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEventAtDefault 10 ef))
      (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEventAtDefault 11 ef)))

private theorem OrderedCauchyGroupTasteGate_single_carrier_alignment_round_trip
    (x : OrderedCauchyGroupUp) :
    orderedCauchyGroupFromEventFlow (orderedCauchyGroupToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A O M S R F L E H C P N =>
      change
        some
          (OrderedCauchyGroupUp.mk
            (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEncodeBHist A))
            (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEncodeBHist O))
            (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEncodeBHist M))
            (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEncodeBHist S))
            (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEncodeBHist R))
            (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEncodeBHist F))
            (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEncodeBHist L))
            (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEncodeBHist E))
            (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEncodeBHist H))
            (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEncodeBHist C))
            (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEncodeBHist P))
            (orderedCauchyGroupDecodeBHist (orderedCauchyGroupEncodeBHist N))) =
          some (OrderedCauchyGroupUp.mk A O M S R F L E H C P N)
      rw [OrderedCauchyGroupTasteGate_single_carrier_alignment_decode A,
        OrderedCauchyGroupTasteGate_single_carrier_alignment_decode O,
        OrderedCauchyGroupTasteGate_single_carrier_alignment_decode M,
        OrderedCauchyGroupTasteGate_single_carrier_alignment_decode S,
        OrderedCauchyGroupTasteGate_single_carrier_alignment_decode R,
        OrderedCauchyGroupTasteGate_single_carrier_alignment_decode F,
        OrderedCauchyGroupTasteGate_single_carrier_alignment_decode L,
        OrderedCauchyGroupTasteGate_single_carrier_alignment_decode E,
        OrderedCauchyGroupTasteGate_single_carrier_alignment_decode H,
        OrderedCauchyGroupTasteGate_single_carrier_alignment_decode C,
        OrderedCauchyGroupTasteGate_single_carrier_alignment_decode P,
        OrderedCauchyGroupTasteGate_single_carrier_alignment_decode N]

private theorem OrderedCauchyGroupTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : OrderedCauchyGroupUp} :
    orderedCauchyGroupToEventFlow x = orderedCauchyGroupToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      orderedCauchyGroupFromEventFlow (orderedCauchyGroupToEventFlow x) =
        orderedCauchyGroupFromEventFlow (orderedCauchyGroupToEventFlow y) :=
    congrArg orderedCauchyGroupFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (OrderedCauchyGroupTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (OrderedCauchyGroupTasteGate_single_carrier_alignment_round_trip y)))

instance orderedCauchyGroupBHistCarrier : BHistCarrier OrderedCauchyGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := orderedCauchyGroupToEventFlow
  fromEventFlow := orderedCauchyGroupFromEventFlow

instance orderedCauchyGroupChapterTasteGate :
    ChapterTasteGate OrderedCauchyGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change orderedCauchyGroupFromEventFlow (orderedCauchyGroupToEventFlow x) = some x
    exact OrderedCauchyGroupTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (OrderedCauchyGroupTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem OrderedCauchyGroupTasteGate_single_carrier_alignment :
    (∀ h : BHist, orderedCauchyGroupDecodeBHist (orderedCauchyGroupEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier OrderedCauchyGroupUp) ∧
        Nonempty (ChapterTasteGate OrderedCauchyGroupUp) ∧
          orderedCauchyGroupEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨OrderedCauchyGroupTasteGate_single_carrier_alignment_decode,
      ⟨orderedCauchyGroupBHistCarrier⟩, ⟨orderedCauchyGroupChapterTasteGate⟩, rfl⟩

end BEDC.Derived.OrderedCauchyGroupUp
