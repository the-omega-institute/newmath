import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbelSummationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbelSummationUp : Type where
  | mk (S A D B T R E H C P N : BHist) : AbelSummationUp
  deriving DecidableEq

def abelSummationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: abelSummationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: abelSummationEncodeBHist h

def abelSummationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (abelSummationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (abelSummationDecodeBHist tail)

private theorem abelSummationDecode_encode :
    ∀ h : BHist, abelSummationDecodeBHist (abelSummationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def abelSummationToEventFlow : AbelSummationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AbelSummationUp.mk S A D B T R E H C P N =>
      [abelSummationEncodeBHist S,
        abelSummationEncodeBHist A,
        abelSummationEncodeBHist D,
        abelSummationEncodeBHist B,
        abelSummationEncodeBHist T,
        abelSummationEncodeBHist R,
        abelSummationEncodeBHist E,
        abelSummationEncodeBHist H,
        abelSummationEncodeBHist C,
        abelSummationEncodeBHist P,
        abelSummationEncodeBHist N]

def abelSummationFromEventFlow : EventFlow → Option AbelSummationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest =>
      match rest with
      | [] => none
      | A :: rest =>
          match rest with
          | [] => none
          | D :: rest =>
              match rest with
              | [] => none
              | B :: rest =>
                  match rest with
                  | [] => none
                  | T :: rest =>
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
                                                    (AbelSummationUp.mk
                                                      (abelSummationDecodeBHist S)
                                                      (abelSummationDecodeBHist A)
                                                      (abelSummationDecodeBHist D)
                                                      (abelSummationDecodeBHist B)
                                                      (abelSummationDecodeBHist T)
                                                      (abelSummationDecodeBHist R)
                                                      (abelSummationDecodeBHist E)
                                                      (abelSummationDecodeBHist H)
                                                      (abelSummationDecodeBHist C)
                                                      (abelSummationDecodeBHist P)
                                                      (abelSummationDecodeBHist N))
                                              | _ :: _ => none

private theorem abelSummation_round_trip :
    ∀ x : AbelSummationUp,
      abelSummationFromEventFlow (abelSummationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S A D B T R E H C P N =>
      rw [abelSummationToEventFlow, abelSummationFromEventFlow,
        abelSummationDecode_encode S,
        abelSummationDecode_encode A,
        abelSummationDecode_encode D,
        abelSummationDecode_encode B,
        abelSummationDecode_encode T,
        abelSummationDecode_encode R,
        abelSummationDecode_encode E,
        abelSummationDecode_encode H,
        abelSummationDecode_encode C,
        abelSummationDecode_encode P,
        abelSummationDecode_encode N]

private theorem abelSummationToEventFlow_injective {x y : AbelSummationUp} :
    abelSummationToEventFlow x = abelSummationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      abelSummationFromEventFlow (abelSummationToEventFlow x) =
        abelSummationFromEventFlow (abelSummationToEventFlow y) :=
    congrArg abelSummationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (abelSummation_round_trip x).symm
      (Eq.trans hread (abelSummation_round_trip y)))

instance abelSummationBHistCarrier : BHistCarrier AbelSummationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := abelSummationToEventFlow
  fromEventFlow := abelSummationFromEventFlow

instance abelSummationChapterTasteGate : ChapterTasteGate AbelSummationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change abelSummationFromEventFlow (abelSummationToEventFlow x) = some x
    exact abelSummation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (abelSummationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate AbelSummationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  abelSummationChapterTasteGate

theorem AbelSummationUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, abelSummationDecodeBHist (abelSummationEncodeBHist h) = h) ∧
      (∀ x : AbelSummationUp,
        abelSummationFromEventFlow (abelSummationToEventFlow x) = some x) ∧
      (∀ x y : AbelSummationUp,
        abelSummationToEventFlow x = abelSummationToEventFlow y → x = y) ∧
      abelSummationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨abelSummationDecode_encode,
      abelSummation_round_trip,
      fun _ _ heq => abelSummationToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.AbelSummationUp
