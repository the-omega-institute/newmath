import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformLipschitzFamilyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformLipschitzFamilyUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (X Y I F L V H C P N : BHist) : UniformLipschitzFamilyUp
  deriving DecidableEq

def uniformLipschitzFamilyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformLipschitzFamilyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformLipschitzFamilyEncodeBHist h

def uniformLipschitzFamilyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformLipschitzFamilyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformLipschitzFamilyDecodeBHist tail)

private theorem UniformLipschitzFamilyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      uniformLipschitzFamilyDecodeBHist (uniformLipschitzFamilyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformLipschitzFamilyFields : UniformLipschitzFamilyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformLipschitzFamilyUp.mk X Y I F L V H C P N => [X, Y, I, F, L, V, H, C, P, N]

def uniformLipschitzFamilyToEventFlow : UniformLipschitzFamilyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformLipschitzFamilyFields x).map uniformLipschitzFamilyEncodeBHist

def uniformLipschitzFamilyFromEventFlow :
    EventFlow → Option UniformLipschitzFamilyUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: Y :: I :: F :: L :: V :: H :: C :: P :: N :: [] =>
      some
        (UniformLipschitzFamilyUp.mk
          (uniformLipschitzFamilyDecodeBHist X)
          (uniformLipschitzFamilyDecodeBHist Y)
          (uniformLipschitzFamilyDecodeBHist I)
          (uniformLipschitzFamilyDecodeBHist F)
          (uniformLipschitzFamilyDecodeBHist L)
          (uniformLipschitzFamilyDecodeBHist V)
          (uniformLipschitzFamilyDecodeBHist H)
          (uniformLipschitzFamilyDecodeBHist C)
          (uniformLipschitzFamilyDecodeBHist P)
          (uniformLipschitzFamilyDecodeBHist N))
  | _ => none

private theorem UniformLipschitzFamilyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformLipschitzFamilyUp,
      uniformLipschitzFamilyFromEventFlow (uniformLipschitzFamilyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y I F L V H C P N =>
      change
        some
          (UniformLipschitzFamilyUp.mk
            (uniformLipschitzFamilyDecodeBHist (uniformLipschitzFamilyEncodeBHist X))
            (uniformLipschitzFamilyDecodeBHist (uniformLipschitzFamilyEncodeBHist Y))
            (uniformLipschitzFamilyDecodeBHist (uniformLipschitzFamilyEncodeBHist I))
            (uniformLipschitzFamilyDecodeBHist (uniformLipschitzFamilyEncodeBHist F))
            (uniformLipschitzFamilyDecodeBHist (uniformLipschitzFamilyEncodeBHist L))
            (uniformLipschitzFamilyDecodeBHist (uniformLipschitzFamilyEncodeBHist V))
            (uniformLipschitzFamilyDecodeBHist (uniformLipschitzFamilyEncodeBHist H))
            (uniformLipschitzFamilyDecodeBHist (uniformLipschitzFamilyEncodeBHist C))
            (uniformLipschitzFamilyDecodeBHist (uniformLipschitzFamilyEncodeBHist P))
            (uniformLipschitzFamilyDecodeBHist (uniformLipschitzFamilyEncodeBHist N))) =
          some (UniformLipschitzFamilyUp.mk X Y I F L V H C P N)
      simp only [UniformLipschitzFamilyTasteGate_single_carrier_alignment_decode]

private theorem UniformLipschitzFamilyTasteGate_single_carrier_alignment_injective
    {x y : UniformLipschitzFamilyUp} :
    uniformLipschitzFamilyToEventFlow x = uniformLipschitzFamilyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformLipschitzFamilyFromEventFlow (uniformLipschitzFamilyToEventFlow x) =
        uniformLipschitzFamilyFromEventFlow (uniformLipschitzFamilyToEventFlow y) :=
    congrArg uniformLipschitzFamilyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UniformLipschitzFamilyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformLipschitzFamilyTasteGate_single_carrier_alignment_round_trip y)))

instance uniformLipschitzFamilyBHistCarrier : BHistCarrier UniformLipschitzFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformLipschitzFamilyToEventFlow
  fromEventFlow := uniformLipschitzFamilyFromEventFlow

instance uniformLipschitzFamilyChapterTasteGate :
    ChapterTasteGate UniformLipschitzFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformLipschitzFamilyFromEventFlow (uniformLipschitzFamilyToEventFlow x) = some x
    exact UniformLipschitzFamilyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformLipschitzFamilyTasteGate_single_carrier_alignment_injective heq)

theorem UniformLipschitzFamilyTasteGate_single_carrier_alignment :
    ∀ h : BHist,
      uniformLipschitzFamilyDecodeBHist (uniformLipschitzFamilyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  exact UniformLipschitzFamilyTasteGate_single_carrier_alignment_decode

end BEDC.Derived.UniformLipschitzFamilyUp
