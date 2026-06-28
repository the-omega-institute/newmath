import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformSpaceRealCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformSpaceRealCompletionUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (R U F B S Q E H C P N : BHist) : UniformSpaceRealCompletionUp
  deriving DecidableEq

def uniformSpaceRealCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformSpaceRealCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformSpaceRealCompletionEncodeBHist h

def uniformSpaceRealCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformSpaceRealCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformSpaceRealCompletionDecodeBHist tail)

private theorem UniformSpaceRealCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      uniformSpaceRealCompletionDecodeBHist
          (uniformSpaceRealCompletionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformSpaceRealCompletionFields : UniformSpaceRealCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformSpaceRealCompletionUp.mk R U F B S Q E H C P N =>
      [R, U, F, B, S, Q, E, H, C, P, N]

def uniformSpaceRealCompletionToEventFlow : UniformSpaceRealCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformSpaceRealCompletionFields x).map uniformSpaceRealCompletionEncodeBHist

def uniformSpaceRealCompletionFromEventFlow :
    EventFlow → Option UniformSpaceRealCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | R :: U :: F :: B :: S :: Q :: E :: H :: C :: P :: N :: [] =>
      some
        (UniformSpaceRealCompletionUp.mk
          (uniformSpaceRealCompletionDecodeBHist R)
          (uniformSpaceRealCompletionDecodeBHist U)
          (uniformSpaceRealCompletionDecodeBHist F)
          (uniformSpaceRealCompletionDecodeBHist B)
          (uniformSpaceRealCompletionDecodeBHist S)
          (uniformSpaceRealCompletionDecodeBHist Q)
          (uniformSpaceRealCompletionDecodeBHist E)
          (uniformSpaceRealCompletionDecodeBHist H)
          (uniformSpaceRealCompletionDecodeBHist C)
          (uniformSpaceRealCompletionDecodeBHist P)
          (uniformSpaceRealCompletionDecodeBHist N))
  | _ => none

private theorem UniformSpaceRealCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformSpaceRealCompletionUp,
      uniformSpaceRealCompletionFromEventFlow
          (uniformSpaceRealCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R U F B S Q E H C P N =>
      change
        some
          (UniformSpaceRealCompletionUp.mk
            (uniformSpaceRealCompletionDecodeBHist
              (uniformSpaceRealCompletionEncodeBHist R))
            (uniformSpaceRealCompletionDecodeBHist
              (uniformSpaceRealCompletionEncodeBHist U))
            (uniformSpaceRealCompletionDecodeBHist
              (uniformSpaceRealCompletionEncodeBHist F))
            (uniformSpaceRealCompletionDecodeBHist
              (uniformSpaceRealCompletionEncodeBHist B))
            (uniformSpaceRealCompletionDecodeBHist
              (uniformSpaceRealCompletionEncodeBHist S))
            (uniformSpaceRealCompletionDecodeBHist
              (uniformSpaceRealCompletionEncodeBHist Q))
            (uniformSpaceRealCompletionDecodeBHist
              (uniformSpaceRealCompletionEncodeBHist E))
            (uniformSpaceRealCompletionDecodeBHist
              (uniformSpaceRealCompletionEncodeBHist H))
            (uniformSpaceRealCompletionDecodeBHist
              (uniformSpaceRealCompletionEncodeBHist C))
            (uniformSpaceRealCompletionDecodeBHist
              (uniformSpaceRealCompletionEncodeBHist P))
            (uniformSpaceRealCompletionDecodeBHist
              (uniformSpaceRealCompletionEncodeBHist N))) =
          some (UniformSpaceRealCompletionUp.mk R U F B S Q E H C P N)
      simp only [UniformSpaceRealCompletionTasteGate_single_carrier_alignment_decode]

private theorem UniformSpaceRealCompletionTasteGate_single_carrier_alignment_injective
    {x y : UniformSpaceRealCompletionUp} :
    uniformSpaceRealCompletionToEventFlow x = uniformSpaceRealCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformSpaceRealCompletionFromEventFlow (uniformSpaceRealCompletionToEventFlow x) =
        uniformSpaceRealCompletionFromEventFlow (uniformSpaceRealCompletionToEventFlow y) :=
    congrArg uniformSpaceRealCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformSpaceRealCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformSpaceRealCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance uniformSpaceRealCompletionBHistCarrier :
    BHistCarrier UniformSpaceRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformSpaceRealCompletionToEventFlow
  fromEventFlow := uniformSpaceRealCompletionFromEventFlow

instance uniformSpaceRealCompletionChapterTasteGate :
    ChapterTasteGate UniformSpaceRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformSpaceRealCompletionFromEventFlow (uniformSpaceRealCompletionToEventFlow x) =
        some x
    exact UniformSpaceRealCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformSpaceRealCompletionTasteGate_single_carrier_alignment_injective heq)

theorem UniformSpaceRealCompletionTasteGate_single_carrier_alignment :
    ∀ h : BHist,
      uniformSpaceRealCompletionDecodeBHist
          (uniformSpaceRealCompletionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  exact UniformSpaceRealCompletionTasteGate_single_carrier_alignment_decode

end BEDC.Derived.UniformSpaceRealCompletionUp
