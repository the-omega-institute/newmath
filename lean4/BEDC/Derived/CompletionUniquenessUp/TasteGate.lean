import BEDC.Derived.CompletionUniquenessUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionUniquenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def completionUniquenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionUniquenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionUniquenessEncodeBHist h

def completionUniquenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionUniquenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionUniquenessDecodeBHist tail)

private theorem completionUniqueness_decode_encode :
    ∀ h : BHist, completionUniquenessDecodeBHist (completionUniquenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completionUniquenessToEventFlow : CompletionUniquenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionUniquenessUp.mk D S R E H F L T C P N =>
      [completionUniquenessEncodeBHist D, completionUniquenessEncodeBHist S,
        completionUniquenessEncodeBHist R, completionUniquenessEncodeBHist E,
        completionUniquenessEncodeBHist H, completionUniquenessEncodeBHist F,
        completionUniquenessEncodeBHist L, completionUniquenessEncodeBHist T,
        completionUniquenessEncodeBHist C, completionUniquenessEncodeBHist P,
        completionUniquenessEncodeBHist N]

def completionUniquenessFromEventFlow (flow : EventFlow) : Option CompletionUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | [] => none
  | D :: rest =>
      match rest with
      | [] => none
      | S :: rest =>
          match rest with
          | [] => none
          | R :: rest =>
              match rest with
              | [] => none
              | E :: rest =>
                  match rest with
                  | [] => none
                  | H :: rest =>
                      match rest with
                      | [] => none
                      | F :: rest =>
                          match rest with
                          | [] => none
                          | L :: rest =>
                              match rest with
                              | [] => none
                              | T :: rest =>
                                  match rest with
                                  | [] => none
                                  | C :: rest =>
                                      match rest with
                                      | [] => none
                                      | P :: rest =>
                                          match rest with
                                          | [] => none
                                          | N :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (CompletionUniquenessUp.mk
                                                      (completionUniquenessDecodeBHist D)
                                                      (completionUniquenessDecodeBHist S)
                                                      (completionUniquenessDecodeBHist R)
                                                      (completionUniquenessDecodeBHist E)
                                                      (completionUniquenessDecodeBHist H)
                                                      (completionUniquenessDecodeBHist F)
                                                      (completionUniquenessDecodeBHist L)
                                                      (completionUniquenessDecodeBHist T)
                                                      (completionUniquenessDecodeBHist C)
                                                      (completionUniquenessDecodeBHist P)
                                                      (completionUniquenessDecodeBHist N))
                                              | _ :: _ => none

private theorem completionUniqueness_round_trip :
    ∀ x : CompletionUniquenessUp,
      completionUniquenessFromEventFlow (completionUniquenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R E H F L T C P N =>
      rw [completionUniquenessToEventFlow, completionUniquenessFromEventFlow,
        completionUniqueness_decode_encode D, completionUniqueness_decode_encode S,
        completionUniqueness_decode_encode R, completionUniqueness_decode_encode E,
        completionUniqueness_decode_encode H, completionUniqueness_decode_encode F,
        completionUniqueness_decode_encode L, completionUniqueness_decode_encode T,
        completionUniqueness_decode_encode C, completionUniqueness_decode_encode P,
        completionUniqueness_decode_encode N]

private theorem completionUniquenessToEventFlow_injective
    {x y : CompletionUniquenessUp} :
    completionUniquenessToEventFlow x = completionUniquenessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionUniquenessFromEventFlow (completionUniquenessToEventFlow x) =
        completionUniquenessFromEventFlow (completionUniquenessToEventFlow y) :=
    congrArg completionUniquenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (completionUniqueness_round_trip x).symm
      (Eq.trans hread (completionUniqueness_round_trip y)))

instance completionUniquenessBHistCarrier : BHistCarrier CompletionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionUniquenessToEventFlow
  fromEventFlow := completionUniquenessFromEventFlow

instance completionUniquenessChapterTasteGate :
    ChapterTasteGate CompletionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completionUniquenessFromEventFlow (completionUniquenessToEventFlow x) = some x
    exact completionUniqueness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (completionUniquenessToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompletionUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completionUniquenessChapterTasteGate

theorem CompletionUniquenessTasteGate_single_carrier_alignment :
    (∀ h : BHist, completionUniquenessDecodeBHist (completionUniquenessEncodeBHist h) = h) ∧
      (∀ x : CompletionUniquenessUp,
        completionUniquenessFromEventFlow (completionUniquenessToEventFlow x) = some x) ∧
      (∀ x y : CompletionUniquenessUp,
        completionUniquenessToEventFlow x = completionUniquenessToEventFlow y → x = y) ∧
      completionUniquenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨completionUniqueness_decode_encode,
      completionUniqueness_round_trip,
      fun _ _ heq => completionUniquenessToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CompletionUniquenessUp
