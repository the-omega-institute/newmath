import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PathConnectedSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PathConnectedSpaceUp : Type where
  | mk (E F V C G L H R P N : BHist) : PathConnectedSpaceUp
  deriving DecidableEq

def pathConnectedSpaceEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: pathConnectedSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: pathConnectedSpaceEncodeBHist h

def pathConnectedSpaceDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (pathConnectedSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (pathConnectedSpaceDecodeBHist tail)

private theorem PathConnectedSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, pathConnectedSpaceDecodeBHist (pathConnectedSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def pathConnectedSpaceFields : PathConnectedSpaceUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | PathConnectedSpaceUp.mk E F V C G L H R P N => [E, F, V, C, G, L, H, R, P, N]

def pathConnectedSpaceToEventFlow : PathConnectedSpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (pathConnectedSpaceFields x).map pathConnectedSpaceEncodeBHist

private def pathConnectedSpaceEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => pathConnectedSpaceEventAt index rest

def pathConnectedSpaceFromEventFlow (ef : EventFlow) : Option PathConnectedSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PathConnectedSpaceUp.mk
      (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEventAt 0 ef))
      (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEventAt 1 ef))
      (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEventAt 2 ef))
      (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEventAt 3 ef))
      (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEventAt 4 ef))
      (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEventAt 5 ef))
      (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEventAt 6 ef))
      (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEventAt 7 ef))
      (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEventAt 8 ef))
      (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEventAt 9 ef)))

private theorem PathConnectedSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PathConnectedSpaceUp,
      pathConnectedSpaceFromEventFlow (pathConnectedSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E F V C G L H R P N =>
      change
        some
            (PathConnectedSpaceUp.mk
              (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEncodeBHist E))
              (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEncodeBHist F))
              (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEncodeBHist V))
              (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEncodeBHist C))
              (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEncodeBHist G))
              (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEncodeBHist L))
              (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEncodeBHist H))
              (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEncodeBHist R))
              (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEncodeBHist P))
              (pathConnectedSpaceDecodeBHist (pathConnectedSpaceEncodeBHist N))) =
          some (PathConnectedSpaceUp.mk E F V C G L H R P N)
      rw [PathConnectedSpaceTasteGate_single_carrier_alignment_decode E,
        PathConnectedSpaceTasteGate_single_carrier_alignment_decode F,
        PathConnectedSpaceTasteGate_single_carrier_alignment_decode V,
        PathConnectedSpaceTasteGate_single_carrier_alignment_decode C,
        PathConnectedSpaceTasteGate_single_carrier_alignment_decode G,
        PathConnectedSpaceTasteGate_single_carrier_alignment_decode L,
        PathConnectedSpaceTasteGate_single_carrier_alignment_decode H,
        PathConnectedSpaceTasteGate_single_carrier_alignment_decode R,
        PathConnectedSpaceTasteGate_single_carrier_alignment_decode P,
        PathConnectedSpaceTasteGate_single_carrier_alignment_decode N]

private theorem pathConnectedSpaceToEventFlow_injective {x y : PathConnectedSpaceUp} :
    pathConnectedSpaceToEventFlow x = pathConnectedSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      pathConnectedSpaceFromEventFlow (pathConnectedSpaceToEventFlow x) =
        pathConnectedSpaceFromEventFlow (pathConnectedSpaceToEventFlow y) :=
    congrArg pathConnectedSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PathConnectedSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PathConnectedSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem pathConnectedSpace_field_faithful :
    ∀ x y : PathConnectedSpaceUp, pathConnectedSpaceFields x = pathConnectedSpaceFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E1 F1 V1 C1 G1 L1 H1 R1 P1 N1 =>
      cases y with
      | mk E2 F2 V2 C2 G2 L2 H2 R2 P2 N2 =>
          cases hfields
          rfl

instance pathConnectedSpaceBHistCarrier : BHistCarrier PathConnectedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := pathConnectedSpaceToEventFlow
  fromEventFlow := pathConnectedSpaceFromEventFlow

instance pathConnectedSpaceChapterTasteGate : ChapterTasteGate PathConnectedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change pathConnectedSpaceFromEventFlow (pathConnectedSpaceToEventFlow x) = some x
    exact PathConnectedSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (pathConnectedSpaceToEventFlow_injective heq)

instance pathConnectedSpaceFieldFaithful : FieldFaithful PathConnectedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := pathConnectedSpaceFields
  field_faithful := pathConnectedSpace_field_faithful

instance pathConnectedSpaceNontrivial : Nontrivial PathConnectedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PathConnectedSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      PathConnectedSpaceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem PathConnectedSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, pathConnectedSpaceDecodeBHist (pathConnectedSpaceEncodeBHist h) = h) ∧
      (∀ x : PathConnectedSpaceUp,
        pathConnectedSpaceFromEventFlow (pathConnectedSpaceToEventFlow x) = some x) ∧
      (∀ x y : PathConnectedSpaceUp,
        pathConnectedSpaceToEventFlow x = pathConnectedSpaceToEventFlow y → x = y) ∧
      pathConnectedSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨PathConnectedSpaceTasteGate_single_carrier_alignment_decode,
      PathConnectedSpaceTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => pathConnectedSpaceToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.PathConnectedSpaceUp
