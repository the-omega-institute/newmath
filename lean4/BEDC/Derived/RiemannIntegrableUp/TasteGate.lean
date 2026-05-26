import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannIntegrableUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannIntegrableUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (D M L U G T H C P N : BHist) : RiemannIntegrableUp
  deriving DecidableEq

def riemannIntegrableEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannIntegrableEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannIntegrableEncodeBHist h

def riemannIntegrableDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannIntegrableDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannIntegrableDecodeBHist tail)

private theorem RiemannIntegrableTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, riemannIntegrableDecodeBHist (riemannIntegrableEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def riemannIntegrableFields : RiemannIntegrableUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannIntegrableUp.mk D M L U G T H C P N => [D, M, L, U, G, T, H, C, P, N]

def riemannIntegrableToEventFlow : RiemannIntegrableUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (riemannIntegrableFields x).map riemannIntegrableEncodeBHist

private def RiemannIntegrableTasteGate_single_carrier_alignment_eventAt :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RiemannIntegrableTasteGate_single_carrier_alignment_eventAt index rest

def riemannIntegrableFromEventFlow : EventFlow -> Option RiemannIntegrableUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RiemannIntegrableUp.mk
        (riemannIntegrableDecodeBHist
          (RiemannIntegrableTasteGate_single_carrier_alignment_eventAt 0 ef))
        (riemannIntegrableDecodeBHist
          (RiemannIntegrableTasteGate_single_carrier_alignment_eventAt 1 ef))
        (riemannIntegrableDecodeBHist
          (RiemannIntegrableTasteGate_single_carrier_alignment_eventAt 2 ef))
        (riemannIntegrableDecodeBHist
          (RiemannIntegrableTasteGate_single_carrier_alignment_eventAt 3 ef))
        (riemannIntegrableDecodeBHist
          (RiemannIntegrableTasteGate_single_carrier_alignment_eventAt 4 ef))
        (riemannIntegrableDecodeBHist
          (RiemannIntegrableTasteGate_single_carrier_alignment_eventAt 5 ef))
        (riemannIntegrableDecodeBHist
          (RiemannIntegrableTasteGate_single_carrier_alignment_eventAt 6 ef))
        (riemannIntegrableDecodeBHist
          (RiemannIntegrableTasteGate_single_carrier_alignment_eventAt 7 ef))
        (riemannIntegrableDecodeBHist
          (RiemannIntegrableTasteGate_single_carrier_alignment_eventAt 8 ef))
        (riemannIntegrableDecodeBHist
          (RiemannIntegrableTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem RiemannIntegrableTasteGate_single_carrier_alignment_round_trip :
    forall x : RiemannIntegrableUp,
      riemannIntegrableFromEventFlow (riemannIntegrableToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D M L U G T H C P N =>
      change
        some
          (RiemannIntegrableUp.mk
            (riemannIntegrableDecodeBHist (riemannIntegrableEncodeBHist D))
            (riemannIntegrableDecodeBHist (riemannIntegrableEncodeBHist M))
            (riemannIntegrableDecodeBHist (riemannIntegrableEncodeBHist L))
            (riemannIntegrableDecodeBHist (riemannIntegrableEncodeBHist U))
            (riemannIntegrableDecodeBHist (riemannIntegrableEncodeBHist G))
            (riemannIntegrableDecodeBHist (riemannIntegrableEncodeBHist T))
            (riemannIntegrableDecodeBHist (riemannIntegrableEncodeBHist H))
            (riemannIntegrableDecodeBHist (riemannIntegrableEncodeBHist C))
            (riemannIntegrableDecodeBHist (riemannIntegrableEncodeBHist P))
            (riemannIntegrableDecodeBHist (riemannIntegrableEncodeBHist N))) =
          some (RiemannIntegrableUp.mk D M L U G T H C P N)
      rw [RiemannIntegrableTasteGate_single_carrier_alignment_decode_encode D,
        RiemannIntegrableTasteGate_single_carrier_alignment_decode_encode M,
        RiemannIntegrableTasteGate_single_carrier_alignment_decode_encode L,
        RiemannIntegrableTasteGate_single_carrier_alignment_decode_encode U,
        RiemannIntegrableTasteGate_single_carrier_alignment_decode_encode G,
        RiemannIntegrableTasteGate_single_carrier_alignment_decode_encode T,
        RiemannIntegrableTasteGate_single_carrier_alignment_decode_encode H,
        RiemannIntegrableTasteGate_single_carrier_alignment_decode_encode C,
        RiemannIntegrableTasteGate_single_carrier_alignment_decode_encode P,
        RiemannIntegrableTasteGate_single_carrier_alignment_decode_encode N]

private theorem RiemannIntegrableTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RiemannIntegrableUp} :
    riemannIntegrableToEventFlow x = riemannIntegrableToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      riemannIntegrableFromEventFlow (riemannIntegrableToEventFlow x) =
        riemannIntegrableFromEventFlow (riemannIntegrableToEventFlow y) :=
    congrArg riemannIntegrableFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RiemannIntegrableTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RiemannIntegrableTasteGate_single_carrier_alignment_round_trip y)))

instance riemannIntegrableBHistCarrier : BHistCarrier RiemannIntegrableUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := riemannIntegrableToEventFlow
  fromEventFlow := riemannIntegrableFromEventFlow

instance riemannIntegrableChapterTasteGate : ChapterTasteGate RiemannIntegrableUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change riemannIntegrableFromEventFlow (riemannIntegrableToEventFlow x) = some x
    exact RiemannIntegrableTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RiemannIntegrableTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RiemannIntegrableUp :=
  -- BEDC touchpoint anchor: BHist BMark
  riemannIntegrableChapterTasteGate

theorem RiemannIntegrableTasteGate_single_carrier_alignment :
    (forall h : BHist, riemannIntegrableDecodeBHist (riemannIntegrableEncodeBHist h) = h) ∧
      (forall x : RiemannIntegrableUp,
        riemannIntegrableFromEventFlow (riemannIntegrableToEventFlow x) = some x) ∧
        (forall x y : RiemannIntegrableUp,
          riemannIntegrableToEventFlow x = riemannIntegrableToEventFlow y -> x = y) ∧
          riemannIntegrableEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RiemannIntegrableTasteGate_single_carrier_alignment_decode_encode,
      RiemannIntegrableTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RiemannIntegrableTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RiemannIntegrableUp
