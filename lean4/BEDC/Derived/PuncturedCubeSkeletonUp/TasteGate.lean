import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PuncturedCubeSkeletonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PuncturedCubeSkeletonUp : Type where
  | mk (W A C B G E H T Q R N : BHist) : PuncturedCubeSkeletonUp
  deriving DecidableEq

def puncturedCubeSkeletonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: puncturedCubeSkeletonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: puncturedCubeSkeletonEncodeBHist h

def puncturedCubeSkeletonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (puncturedCubeSkeletonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (puncturedCubeSkeletonDecodeBHist tail)

private theorem PuncturedCubeSkeletonTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      puncturedCubeSkeletonDecodeBHist (puncturedCubeSkeletonEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def puncturedCubeSkeletonFields : PuncturedCubeSkeletonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PuncturedCubeSkeletonUp.mk W A C B G E H T Q R N =>
      [W, A, C, B, G, E, H, T, Q, R, N]

def puncturedCubeSkeletonToEventFlow : PuncturedCubeSkeletonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (puncturedCubeSkeletonFields x).map puncturedCubeSkeletonEncodeBHist

private def puncturedCubeSkeletonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => puncturedCubeSkeletonEventAtDefault index rest

def puncturedCubeSkeletonFromEventFlow
    (ef : EventFlow) : Option PuncturedCubeSkeletonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PuncturedCubeSkeletonUp.mk
      (puncturedCubeSkeletonDecodeBHist (puncturedCubeSkeletonEventAtDefault 0 ef))
      (puncturedCubeSkeletonDecodeBHist (puncturedCubeSkeletonEventAtDefault 1 ef))
      (puncturedCubeSkeletonDecodeBHist (puncturedCubeSkeletonEventAtDefault 2 ef))
      (puncturedCubeSkeletonDecodeBHist (puncturedCubeSkeletonEventAtDefault 3 ef))
      (puncturedCubeSkeletonDecodeBHist (puncturedCubeSkeletonEventAtDefault 4 ef))
      (puncturedCubeSkeletonDecodeBHist (puncturedCubeSkeletonEventAtDefault 5 ef))
      (puncturedCubeSkeletonDecodeBHist (puncturedCubeSkeletonEventAtDefault 6 ef))
      (puncturedCubeSkeletonDecodeBHist (puncturedCubeSkeletonEventAtDefault 7 ef))
      (puncturedCubeSkeletonDecodeBHist (puncturedCubeSkeletonEventAtDefault 8 ef))
      (puncturedCubeSkeletonDecodeBHist (puncturedCubeSkeletonEventAtDefault 9 ef))
      (puncturedCubeSkeletonDecodeBHist (puncturedCubeSkeletonEventAtDefault 10 ef)))

private theorem PuncturedCubeSkeletonTasteGate_single_carrier_alignment_round_trip
    (x : PuncturedCubeSkeletonUp) :
    puncturedCubeSkeletonFromEventFlow (puncturedCubeSkeletonToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk W A C B G E H T Q R N =>
      change
        some
          (PuncturedCubeSkeletonUp.mk
            (puncturedCubeSkeletonDecodeBHist
              (puncturedCubeSkeletonEncodeBHist W))
            (puncturedCubeSkeletonDecodeBHist
              (puncturedCubeSkeletonEncodeBHist A))
            (puncturedCubeSkeletonDecodeBHist
              (puncturedCubeSkeletonEncodeBHist C))
            (puncturedCubeSkeletonDecodeBHist
              (puncturedCubeSkeletonEncodeBHist B))
            (puncturedCubeSkeletonDecodeBHist
              (puncturedCubeSkeletonEncodeBHist G))
            (puncturedCubeSkeletonDecodeBHist
              (puncturedCubeSkeletonEncodeBHist E))
            (puncturedCubeSkeletonDecodeBHist
              (puncturedCubeSkeletonEncodeBHist H))
            (puncturedCubeSkeletonDecodeBHist
              (puncturedCubeSkeletonEncodeBHist T))
            (puncturedCubeSkeletonDecodeBHist
              (puncturedCubeSkeletonEncodeBHist Q))
            (puncturedCubeSkeletonDecodeBHist
              (puncturedCubeSkeletonEncodeBHist R))
            (puncturedCubeSkeletonDecodeBHist
              (puncturedCubeSkeletonEncodeBHist N))) =
          some (PuncturedCubeSkeletonUp.mk W A C B G E H T Q R N)
      rw [PuncturedCubeSkeletonTasteGate_single_carrier_alignment_decode_encode W,
        PuncturedCubeSkeletonTasteGate_single_carrier_alignment_decode_encode A,
        PuncturedCubeSkeletonTasteGate_single_carrier_alignment_decode_encode C,
        PuncturedCubeSkeletonTasteGate_single_carrier_alignment_decode_encode B,
        PuncturedCubeSkeletonTasteGate_single_carrier_alignment_decode_encode G,
        PuncturedCubeSkeletonTasteGate_single_carrier_alignment_decode_encode E,
        PuncturedCubeSkeletonTasteGate_single_carrier_alignment_decode_encode H,
        PuncturedCubeSkeletonTasteGate_single_carrier_alignment_decode_encode T,
        PuncturedCubeSkeletonTasteGate_single_carrier_alignment_decode_encode Q,
        PuncturedCubeSkeletonTasteGate_single_carrier_alignment_decode_encode R,
        PuncturedCubeSkeletonTasteGate_single_carrier_alignment_decode_encode N]

private theorem PuncturedCubeSkeletonTasteGate_single_carrier_alignment_injective
    {x y : PuncturedCubeSkeletonUp} :
    puncturedCubeSkeletonToEventFlow x = puncturedCubeSkeletonToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      puncturedCubeSkeletonFromEventFlow (puncturedCubeSkeletonToEventFlow x) =
        puncturedCubeSkeletonFromEventFlow (puncturedCubeSkeletonToEventFlow y) :=
    congrArg puncturedCubeSkeletonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PuncturedCubeSkeletonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PuncturedCubeSkeletonTasteGate_single_carrier_alignment_round_trip y)))

private theorem PuncturedCubeSkeletonTasteGate_single_carrier_alignment_fields :
    ∀ x y : PuncturedCubeSkeletonUp,
      puncturedCubeSkeletonFields x = puncturedCubeSkeletonFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W₁ A₁ C₁ B₁ G₁ E₁ H₁ T₁ Q₁ R₁ N₁ =>
      cases y with
      | mk W₂ A₂ C₂ B₂ G₂ E₂ H₂ T₂ Q₂ R₂ N₂ =>
          cases hfields
          rfl

instance puncturedCubeSkeletonBHistCarrier :
    BHistCarrier PuncturedCubeSkeletonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := puncturedCubeSkeletonToEventFlow
  fromEventFlow := puncturedCubeSkeletonFromEventFlow

instance puncturedCubeSkeletonChapterTasteGate :
    ChapterTasteGate PuncturedCubeSkeletonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      puncturedCubeSkeletonFromEventFlow (puncturedCubeSkeletonToEventFlow x) =
        some x
    exact PuncturedCubeSkeletonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (PuncturedCubeSkeletonTasteGate_single_carrier_alignment_injective heq)

instance puncturedCubeSkeletonFieldFaithful :
    FieldFaithful PuncturedCubeSkeletonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := puncturedCubeSkeletonFields
  field_faithful := PuncturedCubeSkeletonTasteGate_single_carrier_alignment_fields

instance puncturedCubeSkeletonNontrivial :
    BEDC.Meta.TasteGate.Nontrivial PuncturedCubeSkeletonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PuncturedCubeSkeletonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      PuncturedCubeSkeletonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def PuncturedCubeSkeletonTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate PuncturedCubeSkeletonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  puncturedCubeSkeletonChapterTasteGate

theorem PuncturedCubeSkeletonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      puncturedCubeSkeletonDecodeBHist (puncturedCubeSkeletonEncodeBHist h) = h) ∧
      (∀ x : PuncturedCubeSkeletonUp,
        puncturedCubeSkeletonFromEventFlow (puncturedCubeSkeletonToEventFlow x) =
          some x) ∧
        (∀ x y : PuncturedCubeSkeletonUp,
          puncturedCubeSkeletonToEventFlow x = puncturedCubeSkeletonToEventFlow y →
            x = y) ∧
          puncturedCubeSkeletonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact PuncturedCubeSkeletonTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact PuncturedCubeSkeletonTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact PuncturedCubeSkeletonTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.PuncturedCubeSkeletonUp
