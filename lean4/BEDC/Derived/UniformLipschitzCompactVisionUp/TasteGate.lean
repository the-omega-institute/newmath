import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformLipschitzCompactVisionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformLipschitzCompactVisionUp : Type where
  | mk (K F L U B S M H C P N : BHist) : UniformLipschitzCompactVisionUp
  deriving DecidableEq

def uniformLipschitzCompactVisionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformLipschitzCompactVisionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformLipschitzCompactVisionEncodeBHist h

def uniformLipschitzCompactVisionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformLipschitzCompactVisionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformLipschitzCompactVisionDecodeBHist tail)

private theorem uniformLipschitzCompactVision_decode_encode :
    ∀ h : BHist,
      uniformLipschitzCompactVisionDecodeBHist
          (uniformLipschitzCompactVisionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def uniformLipschitzCompactVisionFields :
    UniformLipschitzCompactVisionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformLipschitzCompactVisionUp.mk K F L U B S M H C P N =>
      [K, F, L, U, B, S, M, H, C, P, N]

def uniformLipschitzCompactVisionToEventFlow :
    UniformLipschitzCompactVisionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (uniformLipschitzCompactVisionFields x).map
        uniformLipschitzCompactVisionEncodeBHist

private def uniformLipschitzCompactVisionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformLipschitzCompactVisionEventAt index rest

def uniformLipschitzCompactVisionFromEventFlow
    (ef : EventFlow) : Option UniformLipschitzCompactVisionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformLipschitzCompactVisionUp.mk
      (uniformLipschitzCompactVisionDecodeBHist
        (uniformLipschitzCompactVisionEventAt 0 ef))
      (uniformLipschitzCompactVisionDecodeBHist
        (uniformLipschitzCompactVisionEventAt 1 ef))
      (uniformLipschitzCompactVisionDecodeBHist
        (uniformLipschitzCompactVisionEventAt 2 ef))
      (uniformLipschitzCompactVisionDecodeBHist
        (uniformLipschitzCompactVisionEventAt 3 ef))
      (uniformLipschitzCompactVisionDecodeBHist
        (uniformLipschitzCompactVisionEventAt 4 ef))
      (uniformLipschitzCompactVisionDecodeBHist
        (uniformLipschitzCompactVisionEventAt 5 ef))
      (uniformLipschitzCompactVisionDecodeBHist
        (uniformLipschitzCompactVisionEventAt 6 ef))
      (uniformLipschitzCompactVisionDecodeBHist
        (uniformLipschitzCompactVisionEventAt 7 ef))
      (uniformLipschitzCompactVisionDecodeBHist
        (uniformLipschitzCompactVisionEventAt 8 ef))
      (uniformLipschitzCompactVisionDecodeBHist
        (uniformLipschitzCompactVisionEventAt 9 ef))
      (uniformLipschitzCompactVisionDecodeBHist
        (uniformLipschitzCompactVisionEventAt 10 ef)))

private theorem uniformLipschitzCompactVision_round_trip
    (x : UniformLipschitzCompactVisionUp) :
    uniformLipschitzCompactVisionFromEventFlow
        (uniformLipschitzCompactVisionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F L U B S M H C P N =>
      change
        some
          (UniformLipschitzCompactVisionUp.mk
            (uniformLipschitzCompactVisionDecodeBHist
              (uniformLipschitzCompactVisionEncodeBHist K))
            (uniformLipschitzCompactVisionDecodeBHist
              (uniformLipschitzCompactVisionEncodeBHist F))
            (uniformLipschitzCompactVisionDecodeBHist
              (uniformLipschitzCompactVisionEncodeBHist L))
            (uniformLipschitzCompactVisionDecodeBHist
              (uniformLipschitzCompactVisionEncodeBHist U))
            (uniformLipschitzCompactVisionDecodeBHist
              (uniformLipschitzCompactVisionEncodeBHist B))
            (uniformLipschitzCompactVisionDecodeBHist
              (uniformLipschitzCompactVisionEncodeBHist S))
            (uniformLipschitzCompactVisionDecodeBHist
              (uniformLipschitzCompactVisionEncodeBHist M))
            (uniformLipschitzCompactVisionDecodeBHist
              (uniformLipschitzCompactVisionEncodeBHist H))
            (uniformLipschitzCompactVisionDecodeBHist
              (uniformLipschitzCompactVisionEncodeBHist C))
            (uniformLipschitzCompactVisionDecodeBHist
              (uniformLipschitzCompactVisionEncodeBHist P))
            (uniformLipschitzCompactVisionDecodeBHist
              (uniformLipschitzCompactVisionEncodeBHist N))) =
          some (UniformLipschitzCompactVisionUp.mk K F L U B S M H C P N)
      rw [uniformLipschitzCompactVision_decode_encode K,
        uniformLipschitzCompactVision_decode_encode F,
        uniformLipschitzCompactVision_decode_encode L,
        uniformLipschitzCompactVision_decode_encode U,
        uniformLipschitzCompactVision_decode_encode B,
        uniformLipschitzCompactVision_decode_encode S,
        uniformLipschitzCompactVision_decode_encode M,
        uniformLipschitzCompactVision_decode_encode H,
        uniformLipschitzCompactVision_decode_encode C,
        uniformLipschitzCompactVision_decode_encode P,
        uniformLipschitzCompactVision_decode_encode N]

private theorem uniformLipschitzCompactVisionToEventFlow_injective
    {x y : UniformLipschitzCompactVisionUp} :
    uniformLipschitzCompactVisionToEventFlow x =
        uniformLipschitzCompactVisionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformLipschitzCompactVisionFromEventFlow
          (uniformLipschitzCompactVisionToEventFlow x) =
        uniformLipschitzCompactVisionFromEventFlow
          (uniformLipschitzCompactVisionToEventFlow y) :=
    congrArg uniformLipschitzCompactVisionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformLipschitzCompactVision_round_trip x).symm
      (Eq.trans hread (uniformLipschitzCompactVision_round_trip y)))

instance uniformLipschitzCompactVisionBHistCarrier :
    BHistCarrier UniformLipschitzCompactVisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformLipschitzCompactVisionToEventFlow
  fromEventFlow := uniformLipschitzCompactVisionFromEventFlow

instance uniformLipschitzCompactVisionChapterTasteGate :
    ChapterTasteGate UniformLipschitzCompactVisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformLipschitzCompactVisionFromEventFlow
          (uniformLipschitzCompactVisionToEventFlow x) =
        some x
    exact uniformLipschitzCompactVision_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformLipschitzCompactVisionToEventFlow_injective heq)

theorem UniformLipschitzCompactVisionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier UniformLipschitzCompactVisionUp) ∧
      Nonempty (ChapterTasteGate UniformLipschitzCompactVisionUp) ∧
        (∀ h : BHist,
          uniformLipschitzCompactVisionDecodeBHist
              (uniformLipschitzCompactVisionEncodeBHist h) =
            h) ∧
          uniformLipschitzCompactVisionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨uniformLipschitzCompactVisionBHistCarrier⟩,
      ⟨uniformLipschitzCompactVisionChapterTasteGate⟩,
      uniformLipschitzCompactVision_decode_encode,
      rfl⟩

end BEDC.Derived.UniformLipschitzCompactVisionUp
