import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProjectiveTensorNormUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProjectiveTensorNormUp : Type where
  | mk (E F T D B Q O H C P N : BHist) : ProjectiveTensorNormUp
  deriving DecidableEq

def projectiveTensorNormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: projectiveTensorNormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: projectiveTensorNormEncodeBHist h

def projectiveTensorNormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (projectiveTensorNormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (projectiveTensorNormDecodeBHist tail)

private theorem ProjectiveTensorNormTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      projectiveTensorNormDecodeBHist (projectiveTensorNormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def projectiveTensorNormFields : ProjectiveTensorNormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProjectiveTensorNormUp.mk E F T D B Q O H C P N =>
      [E, F, T, D, B, Q, O, H, C, P, N]

def projectiveTensorNormToEventFlow : ProjectiveTensorNormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (projectiveTensorNormFields x).map projectiveTensorNormEncodeBHist

def projectiveTensorNormFromEventFlow : EventFlow → Option ProjectiveTensorNormUp
  -- BEDC touchpoint anchor: BHist BMark
  | E :: F :: T :: D :: B :: Q :: O :: H :: C :: P :: N :: [] =>
      some
        (ProjectiveTensorNormUp.mk
          (projectiveTensorNormDecodeBHist E)
          (projectiveTensorNormDecodeBHist F)
          (projectiveTensorNormDecodeBHist T)
          (projectiveTensorNormDecodeBHist D)
          (projectiveTensorNormDecodeBHist B)
          (projectiveTensorNormDecodeBHist Q)
          (projectiveTensorNormDecodeBHist O)
          (projectiveTensorNormDecodeBHist H)
          (projectiveTensorNormDecodeBHist C)
          (projectiveTensorNormDecodeBHist P)
          (projectiveTensorNormDecodeBHist N))
  | _ => none

private theorem ProjectiveTensorNormTasteGate_single_carrier_alignment_round_trip
    (x : ProjectiveTensorNormUp) :
    projectiveTensorNormFromEventFlow
      (projectiveTensorNormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk E F T D B Q O H C P N =>
      change
        some
          (ProjectiveTensorNormUp.mk
            (projectiveTensorNormDecodeBHist (projectiveTensorNormEncodeBHist E))
            (projectiveTensorNormDecodeBHist (projectiveTensorNormEncodeBHist F))
            (projectiveTensorNormDecodeBHist (projectiveTensorNormEncodeBHist T))
            (projectiveTensorNormDecodeBHist (projectiveTensorNormEncodeBHist D))
            (projectiveTensorNormDecodeBHist (projectiveTensorNormEncodeBHist B))
            (projectiveTensorNormDecodeBHist (projectiveTensorNormEncodeBHist Q))
            (projectiveTensorNormDecodeBHist (projectiveTensorNormEncodeBHist O))
            (projectiveTensorNormDecodeBHist (projectiveTensorNormEncodeBHist H))
            (projectiveTensorNormDecodeBHist (projectiveTensorNormEncodeBHist C))
            (projectiveTensorNormDecodeBHist (projectiveTensorNormEncodeBHist P))
            (projectiveTensorNormDecodeBHist (projectiveTensorNormEncodeBHist N))) =
          some (ProjectiveTensorNormUp.mk E F T D B Q O H C P N)
      rw [ProjectiveTensorNormTasteGate_single_carrier_alignment_decode_encode E,
        ProjectiveTensorNormTasteGate_single_carrier_alignment_decode_encode F,
        ProjectiveTensorNormTasteGate_single_carrier_alignment_decode_encode T,
        ProjectiveTensorNormTasteGate_single_carrier_alignment_decode_encode D,
        ProjectiveTensorNormTasteGate_single_carrier_alignment_decode_encode B,
        ProjectiveTensorNormTasteGate_single_carrier_alignment_decode_encode Q,
        ProjectiveTensorNormTasteGate_single_carrier_alignment_decode_encode O,
        ProjectiveTensorNormTasteGate_single_carrier_alignment_decode_encode H,
        ProjectiveTensorNormTasteGate_single_carrier_alignment_decode_encode C,
        ProjectiveTensorNormTasteGate_single_carrier_alignment_decode_encode P,
        ProjectiveTensorNormTasteGate_single_carrier_alignment_decode_encode N]

private theorem ProjectiveTensorNormTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ProjectiveTensorNormUp} :
    projectiveTensorNormToEventFlow x = projectiveTensorNormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      projectiveTensorNormFromEventFlow (projectiveTensorNormToEventFlow x) =
        projectiveTensorNormFromEventFlow (projectiveTensorNormToEventFlow y) :=
    congrArg projectiveTensorNormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ProjectiveTensorNormTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ProjectiveTensorNormTasteGate_single_carrier_alignment_round_trip y)))

instance projectiveTensorNormBHistCarrier : BHistCarrier ProjectiveTensorNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := projectiveTensorNormToEventFlow
  fromEventFlow := projectiveTensorNormFromEventFlow

instance projectiveTensorNormChapterTasteGate :
    ChapterTasteGate ProjectiveTensorNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      projectiveTensorNormFromEventFlow (projectiveTensorNormToEventFlow x) = some x
    exact ProjectiveTensorNormTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ProjectiveTensorNormTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate ProjectiveTensorNormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  projectiveTensorNormChapterTasteGate

theorem ProjectiveTensorNormTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      projectiveTensorNormDecodeBHist (projectiveTensorNormEncodeBHist h) = h) ∧
      (∀ E F T D B Q O H C P N : BHist,
        projectiveTensorNormFields
          (ProjectiveTensorNormUp.mk E F T D B Q O H C P N) =
            [E, F, T, D, B, Q, O, H, C, P, N]) ∧
        projectiveTensorNormEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ProjectiveTensorNormTasteGate_single_carrier_alignment_decode_encode,
      (fun _ _ _ _ _ _ _ _ _ _ _ => rfl), rfl⟩

end BEDC.Derived.ProjectiveTensorNormUp.TasteGate
