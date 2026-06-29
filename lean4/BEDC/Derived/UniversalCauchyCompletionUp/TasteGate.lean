import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniversalCauchyCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniversalCauchyCompletionUp : Type where
  | mk (S D E Q Z W R L H C P N : BHist) : UniversalCauchyCompletionUp

def universalCauchyCompletionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: universalCauchyCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: universalCauchyCompletionEncodeBHist h

def universalCauchyCompletionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (universalCauchyCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (universalCauchyCompletionDecodeBHist tail)

private theorem UniversalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      universalCauchyCompletionDecodeBHist (universalCauchyCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def universalCauchyCompletionFields : UniversalCauchyCompletionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniversalCauchyCompletionUp.mk S D E Q Z W R L H C P N =>
      [S, D, E, Q, Z, W, R, L, H, C, P, N]

def universalCauchyCompletionToEventFlow : UniversalCauchyCompletionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (universalCauchyCompletionFields x).map universalCauchyCompletionEncodeBHist

def universalCauchyCompletionFromEventFlow : EventFlow -> Option UniversalCauchyCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | D :: restD =>
          match restD with
          | E :: restE =>
              match restE with
              | Q :: restQ =>
                  match restQ with
                  | Z :: restZ =>
                      match restZ with
                      | W :: restW =>
                          match restW with
                          | R :: restR =>
                              match restR with
                              | L :: restL =>
                                  match restL with
                                  | H :: restH =>
                                      match restH with
                                      | C :: restC =>
                                          match restC with
                                          | P :: restP =>
                                              match restP with
                                              | N :: restN =>
                                                  match restN with
                                                  | [] =>
                                                      some
                                                        (UniversalCauchyCompletionUp.mk
                                                          (universalCauchyCompletionDecodeBHist S)
                                                          (universalCauchyCompletionDecodeBHist D)
                                                          (universalCauchyCompletionDecodeBHist E)
                                                          (universalCauchyCompletionDecodeBHist Q)
                                                          (universalCauchyCompletionDecodeBHist Z)
                                                          (universalCauchyCompletionDecodeBHist W)
                                                          (universalCauchyCompletionDecodeBHist R)
                                                          (universalCauchyCompletionDecodeBHist L)
                                                          (universalCauchyCompletionDecodeBHist H)
                                                          (universalCauchyCompletionDecodeBHist C)
                                                          (universalCauchyCompletionDecodeBHist P)
                                                          (universalCauchyCompletionDecodeBHist N))
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
      | [] => none
  | [] => none

private theorem UniversalCauchyCompletionTasteGate_single_carrier_alignment_round_trip :
    forall x : UniversalCauchyCompletionUp,
      universalCauchyCompletionFromEventFlow (universalCauchyCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D E Q Z W R L H C P N =>
      change
        some
            (UniversalCauchyCompletionUp.mk
              (universalCauchyCompletionDecodeBHist (universalCauchyCompletionEncodeBHist S))
              (universalCauchyCompletionDecodeBHist (universalCauchyCompletionEncodeBHist D))
              (universalCauchyCompletionDecodeBHist (universalCauchyCompletionEncodeBHist E))
              (universalCauchyCompletionDecodeBHist (universalCauchyCompletionEncodeBHist Q))
              (universalCauchyCompletionDecodeBHist (universalCauchyCompletionEncodeBHist Z))
              (universalCauchyCompletionDecodeBHist (universalCauchyCompletionEncodeBHist W))
              (universalCauchyCompletionDecodeBHist (universalCauchyCompletionEncodeBHist R))
              (universalCauchyCompletionDecodeBHist (universalCauchyCompletionEncodeBHist L))
              (universalCauchyCompletionDecodeBHist (universalCauchyCompletionEncodeBHist H))
              (universalCauchyCompletionDecodeBHist (universalCauchyCompletionEncodeBHist C))
              (universalCauchyCompletionDecodeBHist (universalCauchyCompletionEncodeBHist P))
              (universalCauchyCompletionDecodeBHist (universalCauchyCompletionEncodeBHist N))) =
          some (UniversalCauchyCompletionUp.mk S D E Q Z W R L H C P N)
      rw [UniversalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode S]
      rw [UniversalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode D]
      rw [UniversalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode E]
      rw [UniversalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode Q]
      rw [UniversalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode Z]
      rw [UniversalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode W]
      rw [UniversalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode R]
      rw [UniversalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode L]
      rw [UniversalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode H]
      rw [UniversalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode C]
      rw [UniversalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode P]
      rw [UniversalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem UniversalCauchyCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniversalCauchyCompletionUp} :
    universalCauchyCompletionToEventFlow x = universalCauchyCompletionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      universalCauchyCompletionFromEventFlow (universalCauchyCompletionToEventFlow x) =
        universalCauchyCompletionFromEventFlow (universalCauchyCompletionToEventFlow y) :=
    congrArg universalCauchyCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UniversalCauchyCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UniversalCauchyCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance universalCauchyCompletionBHistCarrier : BHistCarrier UniversalCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := universalCauchyCompletionToEventFlow
  fromEventFlow := universalCauchyCompletionFromEventFlow

instance universalCauchyCompletionChapterTasteGate :
    ChapterTasteGate UniversalCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change universalCauchyCompletionFromEventFlow (universalCauchyCompletionToEventFlow x) = some x
    exact UniversalCauchyCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniversalCauchyCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem UniversalCauchyCompletionTasteGate_single_carrier_alignment :
    (forall h : BHist,
        universalCauchyCompletionDecodeBHist (universalCauchyCompletionEncodeBHist h) = h) ∧
      (forall x : UniversalCauchyCompletionUp,
        universalCauchyCompletionFromEventFlow (universalCauchyCompletionToEventFlow x) = some x) ∧
      (forall x y : UniversalCauchyCompletionUp,
        universalCauchyCompletionToEventFlow x = universalCauchyCompletionToEventFlow y -> x = y) ∧
      universalCauchyCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact UniversalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact UniversalCauchyCompletionTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact UniversalCauchyCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.UniversalCauchyCompletionUp
