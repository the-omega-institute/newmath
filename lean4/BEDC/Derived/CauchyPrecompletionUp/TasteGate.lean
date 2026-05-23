import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyPrecompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyPrecompletionUp : Type where
  | mk (W R D S E H C P N : BHist) : CauchyPrecompletionUp
  deriving DecidableEq

def cauchyPrecompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyPrecompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyPrecompletionEncodeBHist h

def cauchyPrecompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyPrecompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyPrecompletionDecodeBHist tail)

private theorem CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyPrecompletionFields : CauchyPrecompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyPrecompletionUp.mk W R D S E H C P N => [W, R, D, S, E, H, C, P, N]

def cauchyPrecompletionToEventFlow : CauchyPrecompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyPrecompletionFields x).map cauchyPrecompletionEncodeBHist

def cauchyPrecompletionFromEventFlow : EventFlow → Option CauchyPrecompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | W :: restW =>
      match restW with
      | R :: restR =>
          match restR with
          | D :: restD =>
              match restD with
              | S :: restS =>
                  match restS with
                  | E :: restE =>
                      match restE with
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
                                            (CauchyPrecompletionUp.mk
                                              (cauchyPrecompletionDecodeBHist W)
                                              (cauchyPrecompletionDecodeBHist R)
                                              (cauchyPrecompletionDecodeBHist D)
                                              (cauchyPrecompletionDecodeBHist S)
                                              (cauchyPrecompletionDecodeBHist E)
                                              (cauchyPrecompletionDecodeBHist H)
                                              (cauchyPrecompletionDecodeBHist C)
                                              (cauchyPrecompletionDecodeBHist P)
                                              (cauchyPrecompletionDecodeBHist N))
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

private theorem CauchyPrecompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyPrecompletionUp,
      cauchyPrecompletionFromEventFlow (cauchyPrecompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W R D S E H C P N =>
      change
        some
          (CauchyPrecompletionUp.mk
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist W))
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist R))
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist D))
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist S))
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist E))
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist H))
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist C))
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist P))
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist N))) =
          some (CauchyPrecompletionUp.mk W R D S E H C P N)
      rw [CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode W,
        CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode R,
        CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode D,
        CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode S,
        CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode E,
        CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode H,
        CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode C,
        CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode P,
        CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyPrecompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyPrecompletionUp} :
    cauchyPrecompletionToEventFlow x = cauchyPrecompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyPrecompletionFromEventFlow (cauchyPrecompletionToEventFlow x) =
        cauchyPrecompletionFromEventFlow (cauchyPrecompletionToEventFlow y) :=
    congrArg cauchyPrecompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyPrecompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyPrecompletionTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyPrecompletionBHistCarrier : BHistCarrier CauchyPrecompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyPrecompletionToEventFlow
  fromEventFlow := cauchyPrecompletionFromEventFlow

instance cauchyPrecompletionChapterTasteGate : ChapterTasteGate CauchyPrecompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyPrecompletionFromEventFlow (cauchyPrecompletionToEventFlow x) = some x
    exact CauchyPrecompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyPrecompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyPrecompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyPrecompletionChapterTasteGate

theorem CauchyPrecompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist h) = h) ∧
      (∀ x : CauchyPrecompletionUp,
        cauchyPrecompletionFromEventFlow (cauchyPrecompletionToEventFlow x) = some x) ∧
      (∀ x y : CauchyPrecompletionUp,
        cauchyPrecompletionToEventFlow x = cauchyPrecompletionToEventFlow y → x = y) ∧
      cauchyPrecompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact CauchyPrecompletionTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact CauchyPrecompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.CauchyPrecompletionUp
