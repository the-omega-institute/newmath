import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionUniversalPropertyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionUniversalPropertyUp : Type where
  | mk (M D R A F E L P N : BHist) : CompletionUniversalPropertyUp
  deriving DecidableEq

def completionUniversalPropertyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionUniversalPropertyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionUniversalPropertyEncodeBHist h

def completionUniversalPropertyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionUniversalPropertyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionUniversalPropertyDecodeBHist tail)

private theorem CompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      completionUniversalPropertyDecodeBHist
          (completionUniversalPropertyEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completionUniversalPropertyFields : CompletionUniversalPropertyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionUniversalPropertyUp.mk M D R A F E L P N => [M, D, R, A, F, E, L, P, N]

def completionUniversalPropertyToEventFlow : CompletionUniversalPropertyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (completionUniversalPropertyFields x).map completionUniversalPropertyEncodeBHist

def completionUniversalPropertyFromEventFlow : EventFlow → Option CompletionUniversalPropertyUp
  -- BEDC touchpoint anchor: BHist BMark
  | M :: restM =>
      match restM with
      | D :: restD =>
          match restD with
          | R :: restR =>
              match restR with
              | A :: restA =>
                  match restA with
                  | F :: restF =>
                      match restF with
                      | E :: restE =>
                          match restE with
                          | L :: restL =>
                              match restL with
                              | P :: restP =>
                                  match restP with
                                  | N :: rest =>
                                      match rest with
                                      | [] =>
                                          some
                                            (CompletionUniversalPropertyUp.mk
                                              (completionUniversalPropertyDecodeBHist M)
                                              (completionUniversalPropertyDecodeBHist D)
                                              (completionUniversalPropertyDecodeBHist R)
                                              (completionUniversalPropertyDecodeBHist A)
                                              (completionUniversalPropertyDecodeBHist F)
                                              (completionUniversalPropertyDecodeBHist E)
                                              (completionUniversalPropertyDecodeBHist L)
                                              (completionUniversalPropertyDecodeBHist P)
                                              (completionUniversalPropertyDecodeBHist N))
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

private theorem CompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompletionUniversalPropertyUp,
      completionUniversalPropertyFromEventFlow (completionUniversalPropertyToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M D R A F E L P N =>
      change
        some
          (CompletionUniversalPropertyUp.mk
            (completionUniversalPropertyDecodeBHist (completionUniversalPropertyEncodeBHist M))
            (completionUniversalPropertyDecodeBHist (completionUniversalPropertyEncodeBHist D))
            (completionUniversalPropertyDecodeBHist (completionUniversalPropertyEncodeBHist R))
            (completionUniversalPropertyDecodeBHist (completionUniversalPropertyEncodeBHist A))
            (completionUniversalPropertyDecodeBHist (completionUniversalPropertyEncodeBHist F))
            (completionUniversalPropertyDecodeBHist (completionUniversalPropertyEncodeBHist E))
            (completionUniversalPropertyDecodeBHist (completionUniversalPropertyEncodeBHist L))
            (completionUniversalPropertyDecodeBHist (completionUniversalPropertyEncodeBHist P))
            (completionUniversalPropertyDecodeBHist (completionUniversalPropertyEncodeBHist N))) =
          some (CompletionUniversalPropertyUp.mk M D R A F E L P N)
      rw [CompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode M,
        CompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode D,
        CompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode R,
        CompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode A,
        CompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode F,
        CompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode E,
        CompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode L,
        CompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode P,
        CompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompletionUniversalPropertyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompletionUniversalPropertyUp} :
    completionUniversalPropertyToEventFlow x = completionUniversalPropertyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionUniversalPropertyFromEventFlow (completionUniversalPropertyToEventFlow x) =
        completionUniversalPropertyFromEventFlow (completionUniversalPropertyToEventFlow y) :=
    congrArg completionUniversalPropertyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip y)))

instance completionUniversalPropertyBHistCarrier :
    BHistCarrier CompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionUniversalPropertyToEventFlow
  fromEventFlow := completionUniversalPropertyFromEventFlow

instance completionUniversalPropertyChapterTasteGate :
    ChapterTasteGate CompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      completionUniversalPropertyFromEventFlow (completionUniversalPropertyToEventFlow x) =
        some x
    exact CompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompletionUniversalPropertyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompletionUniversalPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completionUniversalPropertyChapterTasteGate

theorem CompletionUniversalPropertyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      completionUniversalPropertyDecodeBHist (completionUniversalPropertyEncodeBHist h) = h) ∧
      (∀ x : CompletionUniversalPropertyUp,
        completionUniversalPropertyFromEventFlow (completionUniversalPropertyToEventFlow x) =
          some x) ∧
      (∀ x y : CompletionUniversalPropertyUp,
        completionUniversalPropertyToEventFlow x = completionUniversalPropertyToEventFlow y →
          x = y) ∧
      completionUniversalPropertyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact CompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact CompletionUniversalPropertyTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.CompletionUniversalPropertyUp
