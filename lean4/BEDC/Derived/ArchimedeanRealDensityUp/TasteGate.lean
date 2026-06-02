import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArchimedeanRealDensityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArchimedeanRealDensityUp : Type where
  | mk (A B W R E G H C P N : BHist) : ArchimedeanRealDensityUp
  deriving DecidableEq

def archimedeanRealDensityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: archimedeanRealDensityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: archimedeanRealDensityEncodeBHist h

def archimedeanRealDensityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (archimedeanRealDensityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (archimedeanRealDensityDecodeBHist tail)

private theorem ArchimedeanRealDensityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, archimedeanRealDensityDecodeBHist (archimedeanRealDensityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def archimedeanRealDensityFields : ArchimedeanRealDensityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanRealDensityUp.mk A B W R E G H C P N => [A, B, W, R, E, G, H, C, P, N]

def archimedeanRealDensityToEventFlow : ArchimedeanRealDensityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (archimedeanRealDensityFields x).map archimedeanRealDensityEncodeBHist

def archimedeanRealDensityFromEventFlow : EventFlow → Option ArchimedeanRealDensityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [A, B, W, R, E, G, H, C, P, N] =>
      some
        (ArchimedeanRealDensityUp.mk
          (archimedeanRealDensityDecodeBHist A)
          (archimedeanRealDensityDecodeBHist B)
          (archimedeanRealDensityDecodeBHist W)
          (archimedeanRealDensityDecodeBHist R)
          (archimedeanRealDensityDecodeBHist E)
          (archimedeanRealDensityDecodeBHist G)
          (archimedeanRealDensityDecodeBHist H)
          (archimedeanRealDensityDecodeBHist C)
          (archimedeanRealDensityDecodeBHist P)
          (archimedeanRealDensityDecodeBHist N))
  | _ => none

private theorem ArchimedeanRealDensityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ArchimedeanRealDensityUp,
      archimedeanRealDensityFromEventFlow (archimedeanRealDensityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B W R E G H C P N =>
      change
        some
          (ArchimedeanRealDensityUp.mk
            (archimedeanRealDensityDecodeBHist (archimedeanRealDensityEncodeBHist A))
            (archimedeanRealDensityDecodeBHist (archimedeanRealDensityEncodeBHist B))
            (archimedeanRealDensityDecodeBHist (archimedeanRealDensityEncodeBHist W))
            (archimedeanRealDensityDecodeBHist (archimedeanRealDensityEncodeBHist R))
            (archimedeanRealDensityDecodeBHist (archimedeanRealDensityEncodeBHist E))
            (archimedeanRealDensityDecodeBHist (archimedeanRealDensityEncodeBHist G))
            (archimedeanRealDensityDecodeBHist (archimedeanRealDensityEncodeBHist H))
            (archimedeanRealDensityDecodeBHist (archimedeanRealDensityEncodeBHist C))
            (archimedeanRealDensityDecodeBHist (archimedeanRealDensityEncodeBHist P))
            (archimedeanRealDensityDecodeBHist (archimedeanRealDensityEncodeBHist N))) =
          some (ArchimedeanRealDensityUp.mk A B W R E G H C P N)
      rw [ArchimedeanRealDensityTasteGate_single_carrier_alignment_decode_encode A,
        ArchimedeanRealDensityTasteGate_single_carrier_alignment_decode_encode B,
        ArchimedeanRealDensityTasteGate_single_carrier_alignment_decode_encode W,
        ArchimedeanRealDensityTasteGate_single_carrier_alignment_decode_encode R,
        ArchimedeanRealDensityTasteGate_single_carrier_alignment_decode_encode E,
        ArchimedeanRealDensityTasteGate_single_carrier_alignment_decode_encode G,
        ArchimedeanRealDensityTasteGate_single_carrier_alignment_decode_encode H,
        ArchimedeanRealDensityTasteGate_single_carrier_alignment_decode_encode C,
        ArchimedeanRealDensityTasteGate_single_carrier_alignment_decode_encode P,
        ArchimedeanRealDensityTasteGate_single_carrier_alignment_decode_encode N]

private theorem ArchimedeanRealDensityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ArchimedeanRealDensityUp} :
    archimedeanRealDensityToEventFlow x = archimedeanRealDensityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      archimedeanRealDensityFromEventFlow (archimedeanRealDensityToEventFlow x) =
        archimedeanRealDensityFromEventFlow (archimedeanRealDensityToEventFlow y) :=
    congrArg archimedeanRealDensityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ArchimedeanRealDensityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ArchimedeanRealDensityTasteGate_single_carrier_alignment_round_trip y)))

instance archimedeanRealDensityBHistCarrier : BHistCarrier ArchimedeanRealDensityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := archimedeanRealDensityToEventFlow
  fromEventFlow := archimedeanRealDensityFromEventFlow

instance archimedeanRealDensityChapterTasteGate :
    ChapterTasteGate ArchimedeanRealDensityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change archimedeanRealDensityFromEventFlow (archimedeanRealDensityToEventFlow x) = some x
    exact ArchimedeanRealDensityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ArchimedeanRealDensityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def ArchimedeanRealDensityTasteGate_single_carrier_alignment :
    (∀ x : ArchimedeanRealDensityUp,
      archimedeanRealDensityFromEventFlow (archimedeanRealDensityToEventFlow x) = some x) ∧
      (∀ x y : ArchimedeanRealDensityUp, x ≠ y →
        archimedeanRealDensityToEventFlow x ≠ archimedeanRealDensityToEventFlow y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro x
    exact ArchimedeanRealDensityTasteGate_single_carrier_alignment_round_trip x
  · intro x y hxy heq
    exact hxy (ArchimedeanRealDensityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

end BEDC.Derived.ArchimedeanRealDensityUp
