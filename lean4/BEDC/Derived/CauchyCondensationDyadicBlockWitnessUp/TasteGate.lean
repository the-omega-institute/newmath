import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCondensationDyadicBlockWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCondensationDyadicBlockWitnessUp : Type where
  | mk (A D W M R E H C P N : BHist) : CauchyCondensationDyadicBlockWitnessUp
  deriving DecidableEq

def cauchyCondensationDyadicBlockWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCondensationDyadicBlockWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCondensationDyadicBlockWitnessEncodeBHist h

def cauchyCondensationDyadicBlockWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCondensationDyadicBlockWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCondensationDyadicBlockWitnessDecodeBHist tail)

private theorem CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode :
    ∀ h : BHist,
      cauchyCondensationDyadicBlockWitnessDecodeBHist
          (cauchyCondensationDyadicBlockWitnessEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCondensationDyadicBlockWitnessFields :
    CauchyCondensationDyadicBlockWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCondensationDyadicBlockWitnessUp.mk A D W M R E H C P N =>
      [A, D, W, M, R, E, H, C, P, N]

def cauchyCondensationDyadicBlockWitnessToEventFlow :
    CauchyCondensationDyadicBlockWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyCondensationDyadicBlockWitnessFields x).map
        cauchyCondensationDyadicBlockWitnessEncodeBHist

def cauchyCondensationDyadicBlockWitnessFromEventFlow :
    EventFlow → Option CauchyCondensationDyadicBlockWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [A, D, W, M, R, E, H, C, P, N] =>
      some
        (CauchyCondensationDyadicBlockWitnessUp.mk
          (cauchyCondensationDyadicBlockWitnessDecodeBHist A)
          (cauchyCondensationDyadicBlockWitnessDecodeBHist D)
          (cauchyCondensationDyadicBlockWitnessDecodeBHist W)
          (cauchyCondensationDyadicBlockWitnessDecodeBHist M)
          (cauchyCondensationDyadicBlockWitnessDecodeBHist R)
          (cauchyCondensationDyadicBlockWitnessDecodeBHist E)
          (cauchyCondensationDyadicBlockWitnessDecodeBHist H)
          (cauchyCondensationDyadicBlockWitnessDecodeBHist C)
          (cauchyCondensationDyadicBlockWitnessDecodeBHist P)
          (cauchyCondensationDyadicBlockWitnessDecodeBHist N))
  | _ => none

private theorem CauchyCondensationDyadicBlockWitnessTasteGate_round_trip :
    ∀ x : CauchyCondensationDyadicBlockWitnessUp,
      cauchyCondensationDyadicBlockWitnessFromEventFlow
          (cauchyCondensationDyadicBlockWitnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A D W M R E H C P N =>
      change
        some
          (CauchyCondensationDyadicBlockWitnessUp.mk
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist A))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist D))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist W))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist M))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist R))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist E))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist H))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist C))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist P))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist N))) =
          some (CauchyCondensationDyadicBlockWitnessUp.mk A D W M R E H C P N)
      rw [CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode A,
        CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode D,
        CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode W,
        CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode M,
        CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode R,
        CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode E,
        CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode H,
        CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode C,
        CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode P,
        CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode N]

private theorem CauchyCondensationDyadicBlockWitnessTasteGate_toEventFlow_injective
    {x y : CauchyCondensationDyadicBlockWitnessUp} :
    cauchyCondensationDyadicBlockWitnessToEventFlow x =
        cauchyCondensationDyadicBlockWitnessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCondensationDyadicBlockWitnessFromEventFlow
          (cauchyCondensationDyadicBlockWitnessToEventFlow x) =
        cauchyCondensationDyadicBlockWitnessFromEventFlow
          (cauchyCondensationDyadicBlockWitnessToEventFlow y) :=
    congrArg cauchyCondensationDyadicBlockWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCondensationDyadicBlockWitnessTasteGate_round_trip x).symm
      (Eq.trans hread (CauchyCondensationDyadicBlockWitnessTasteGate_round_trip y)))

instance cauchyCondensationDyadicBlockWitnessBHistCarrier :
    BHistCarrier CauchyCondensationDyadicBlockWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCondensationDyadicBlockWitnessToEventFlow
  fromEventFlow := cauchyCondensationDyadicBlockWitnessFromEventFlow

instance cauchyCondensationDyadicBlockWitnessChapterTasteGate :
    ChapterTasteGate CauchyCondensationDyadicBlockWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCondensationDyadicBlockWitnessFromEventFlow
          (cauchyCondensationDyadicBlockWitnessToEventFlow x) =
        some x
    exact CauchyCondensationDyadicBlockWitnessTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCondensationDyadicBlockWitnessTasteGate_toEventFlow_injective heq)

theorem CauchyCondensationDyadicBlockWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCondensationDyadicBlockWitnessDecodeBHist
          (cauchyCondensationDyadicBlockWitnessEncodeBHist h) =
        h) ∧
      (∀ x : CauchyCondensationDyadicBlockWitnessUp,
        cauchyCondensationDyadicBlockWitnessFromEventFlow
            (cauchyCondensationDyadicBlockWitnessToEventFlow x) =
          some x) ∧
      (∀ x y : CauchyCondensationDyadicBlockWitnessUp,
        cauchyCondensationDyadicBlockWitnessToEventFlow x =
            cauchyCondensationDyadicBlockWitnessToEventFlow y →
          x = y) ∧
      cauchyCondensationDyadicBlockWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode
  constructor
  · exact CauchyCondensationDyadicBlockWitnessTasteGate_round_trip
  constructor
  · intro x y heq
    exact CauchyCondensationDyadicBlockWitnessTasteGate_toEventFlow_injective heq
  · rfl

end BEDC.Derived.CauchyCondensationDyadicBlockWitnessUp
