import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoxDimensionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoxDimensionUp : Type where
  | mk (M K S C R D N H P L : BHist) : BoxDimensionUp
  deriving DecidableEq

def boxDimensionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boxDimensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boxDimensionEncodeBHist h

def boxDimensionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boxDimensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boxDimensionDecodeBHist tail)

private theorem boxDimension_decode_encode :
    ∀ h : BHist, boxDimensionDecodeBHist (boxDimensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boxDimensionFields : BoxDimensionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoxDimensionUp.mk M K S C R D N H P L => [M, K, S, C, R, D, N, H, P, L]

def boxDimensionToEventFlow : BoxDimensionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (boxDimensionFields token).map boxDimensionEncodeBHist

def boxDimensionFromEventFlow : EventFlow → Option BoxDimensionUp
  -- BEDC touchpoint anchor: BHist BMark
  | M :: restM =>
      match restM with
      | K :: restK =>
          match restK with
          | S :: restS =>
              match restS with
              | C :: restC =>
                  match restC with
                  | R :: restR =>
                      match restR with
                      | D :: restD =>
                          match restD with
                          | N :: restN =>
                              match restN with
                              | H :: restH =>
                                  match restH with
                                  | P :: restP =>
                                      match restP with
                                      | L :: restL =>
                                          match restL with
                                          | [] =>
                                              some
                                                (BoxDimensionUp.mk
                                                  (boxDimensionDecodeBHist M)
                                                  (boxDimensionDecodeBHist K)
                                                  (boxDimensionDecodeBHist S)
                                                  (boxDimensionDecodeBHist C)
                                                  (boxDimensionDecodeBHist R)
                                                  (boxDimensionDecodeBHist D)
                                                  (boxDimensionDecodeBHist N)
                                                  (boxDimensionDecodeBHist H)
                                                  (boxDimensionDecodeBHist P)
                                                  (boxDimensionDecodeBHist L))
                                          | _ :: _ => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem boxDimension_round_trip :
    ∀ token : BoxDimensionUp,
      boxDimensionFromEventFlow (boxDimensionToEventFlow token) = some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk M K S C R D N H P L =>
      change
        some
            (BoxDimensionUp.mk
              (boxDimensionDecodeBHist (boxDimensionEncodeBHist M))
              (boxDimensionDecodeBHist (boxDimensionEncodeBHist K))
              (boxDimensionDecodeBHist (boxDimensionEncodeBHist S))
              (boxDimensionDecodeBHist (boxDimensionEncodeBHist C))
              (boxDimensionDecodeBHist (boxDimensionEncodeBHist R))
              (boxDimensionDecodeBHist (boxDimensionEncodeBHist D))
              (boxDimensionDecodeBHist (boxDimensionEncodeBHist N))
              (boxDimensionDecodeBHist (boxDimensionEncodeBHist H))
              (boxDimensionDecodeBHist (boxDimensionEncodeBHist P))
              (boxDimensionDecodeBHist (boxDimensionEncodeBHist L))) =
          some (BoxDimensionUp.mk M K S C R D N H P L)
      rw [boxDimension_decode_encode M]
      rw [boxDimension_decode_encode K]
      rw [boxDimension_decode_encode S]
      rw [boxDimension_decode_encode C]
      rw [boxDimension_decode_encode R]
      rw [boxDimension_decode_encode D]
      rw [boxDimension_decode_encode N]
      rw [boxDimension_decode_encode H]
      rw [boxDimension_decode_encode P]
      rw [boxDimension_decode_encode L]

private theorem boxDimensionToEventFlow_injective {x y : BoxDimensionUp} :
    boxDimensionToEventFlow x = boxDimensionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boxDimensionFromEventFlow (boxDimensionToEventFlow x) =
        boxDimensionFromEventFlow (boxDimensionToEventFlow y) :=
    congrArg boxDimensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (boxDimension_round_trip x).symm
      (Eq.trans hread (boxDimension_round_trip y)))

instance boxDimensionBHistCarrier : BHistCarrier BoxDimensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boxDimensionToEventFlow
  fromEventFlow := boxDimensionFromEventFlow

instance boxDimensionChapterTasteGate : ChapterTasteGate BoxDimensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boxDimensionFromEventFlow (boxDimensionToEventFlow x) = some x
    exact boxDimension_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boxDimensionToEventFlow_injective heq)

theorem BoxDimensionTasteGate_single_carrier_alignment :
    ChapterTasteGate BoxDimensionUp ∧
      (∀ x : BoxDimensionUp,
        ∃ M K S C R D N H P L : BHist,
          x = BoxDimensionUp.mk M K S C R D N H P L ∧
            boxDimensionFields x = [M, K, S, C, R, D, N, H, P, L] ∧
              boxDimensionFromEventFlow (boxDimensionToEventFlow x) = some x ∧
                boxDimensionEncodeBHist BHist.Empty = ([] : RawEvent) ∧
                  boxDimensionEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0]) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact boxDimensionChapterTasteGate
  · intro x
    cases x with
    | mk M K S C R D N H P L =>
        exact
          ⟨M, K, S, C, R, D, N, H, P, L, rfl, rfl, boxDimension_round_trip _,
            rfl, rfl⟩

end BEDC.Derived.BoxDimensionUp
