import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedBilinearMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedBilinearMapUp : Type where
  | mk (E F G B K L R T P N : BHist) : BoundedBilinearMapUp
  deriving DecidableEq

def boundedBilinearMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedBilinearMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedBilinearMapEncodeBHist h

def boundedBilinearMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedBilinearMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedBilinearMapDecodeBHist tail)

private theorem BoundedBilinearMapTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, boundedBilinearMapDecodeBHist (boundedBilinearMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedBilinearMapFields : BoundedBilinearMapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedBilinearMapUp.mk E F G B K L R T P N => [E, F, G, B, K, L, R, T, P, N]

def boundedBilinearMapToEventFlow : BoundedBilinearMapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedBilinearMapFields x).map boundedBilinearMapEncodeBHist

private def boundedBilinearMapEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedBilinearMapEventAtDefault index rest

def boundedBilinearMapFromEventFlow : EventFlow → Option BoundedBilinearMapUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (BoundedBilinearMapUp.mk
          (boundedBilinearMapDecodeBHist (boundedBilinearMapEventAtDefault 0 ef))
          (boundedBilinearMapDecodeBHist (boundedBilinearMapEventAtDefault 1 ef))
          (boundedBilinearMapDecodeBHist (boundedBilinearMapEventAtDefault 2 ef))
          (boundedBilinearMapDecodeBHist (boundedBilinearMapEventAtDefault 3 ef))
          (boundedBilinearMapDecodeBHist (boundedBilinearMapEventAtDefault 4 ef))
          (boundedBilinearMapDecodeBHist (boundedBilinearMapEventAtDefault 5 ef))
          (boundedBilinearMapDecodeBHist (boundedBilinearMapEventAtDefault 6 ef))
          (boundedBilinearMapDecodeBHist (boundedBilinearMapEventAtDefault 7 ef))
          (boundedBilinearMapDecodeBHist (boundedBilinearMapEventAtDefault 8 ef))
          (boundedBilinearMapDecodeBHist (boundedBilinearMapEventAtDefault 9 ef)))

private theorem BoundedBilinearMapTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedBilinearMapUp,
      boundedBilinearMapFromEventFlow (boundedBilinearMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E F G B K L R T P N =>
      change
        some
          (BoundedBilinearMapUp.mk
            (boundedBilinearMapDecodeBHist (boundedBilinearMapEncodeBHist E))
            (boundedBilinearMapDecodeBHist (boundedBilinearMapEncodeBHist F))
            (boundedBilinearMapDecodeBHist (boundedBilinearMapEncodeBHist G))
            (boundedBilinearMapDecodeBHist (boundedBilinearMapEncodeBHist B))
            (boundedBilinearMapDecodeBHist (boundedBilinearMapEncodeBHist K))
            (boundedBilinearMapDecodeBHist (boundedBilinearMapEncodeBHist L))
            (boundedBilinearMapDecodeBHist (boundedBilinearMapEncodeBHist R))
            (boundedBilinearMapDecodeBHist (boundedBilinearMapEncodeBHist T))
            (boundedBilinearMapDecodeBHist (boundedBilinearMapEncodeBHist P))
            (boundedBilinearMapDecodeBHist (boundedBilinearMapEncodeBHist N))) =
          some (BoundedBilinearMapUp.mk E F G B K L R T P N)
      rw [BoundedBilinearMapTasteGate_single_carrier_alignment_decode E,
        BoundedBilinearMapTasteGate_single_carrier_alignment_decode F,
        BoundedBilinearMapTasteGate_single_carrier_alignment_decode G,
        BoundedBilinearMapTasteGate_single_carrier_alignment_decode B,
        BoundedBilinearMapTasteGate_single_carrier_alignment_decode K,
        BoundedBilinearMapTasteGate_single_carrier_alignment_decode L,
        BoundedBilinearMapTasteGate_single_carrier_alignment_decode R,
        BoundedBilinearMapTasteGate_single_carrier_alignment_decode T,
        BoundedBilinearMapTasteGate_single_carrier_alignment_decode P,
        BoundedBilinearMapTasteGate_single_carrier_alignment_decode N]

private theorem BoundedBilinearMapTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BoundedBilinearMapUp} :
    boundedBilinearMapToEventFlow x = boundedBilinearMapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedBilinearMapFromEventFlow (boundedBilinearMapToEventFlow x) =
        boundedBilinearMapFromEventFlow (boundedBilinearMapToEventFlow y) :=
    congrArg boundedBilinearMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BoundedBilinearMapTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundedBilinearMapTasteGate_single_carrier_alignment_round_trip y)))

instance boundedBilinearMapBHistCarrier : BHistCarrier BoundedBilinearMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedBilinearMapToEventFlow
  fromEventFlow := boundedBilinearMapFromEventFlow

instance boundedBilinearMapChapterTasteGate : ChapterTasteGate BoundedBilinearMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedBilinearMapFromEventFlow (boundedBilinearMapToEventFlow x) = some x
    exact BoundedBilinearMapTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BoundedBilinearMapTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BoundedBilinearMapTasteGate_single_carrier_alignment :
    (∀ h : BHist, boundedBilinearMapDecodeBHist (boundedBilinearMapEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BoundedBilinearMapUp) ∧
        Nonempty (ChapterTasteGate BoundedBilinearMapUp) ∧
          boundedBilinearMapEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BoundedBilinearMapTasteGate_single_carrier_alignment_decode,
      ⟨boundedBilinearMapBHistCarrier⟩,
      ⟨boundedBilinearMapChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BoundedBilinearMapUp
