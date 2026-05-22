import BEDC.Derived.CompletionExtractorUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionExtractorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def completionExtractorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionExtractorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionExtractorEncodeBHist h

def completionExtractorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionExtractorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionExtractorDecodeBHist tail)

private theorem completionExtractorDecodeEncodeBHist :
    ∀ h : BHist, completionExtractorDecodeBHist (completionExtractorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def completionExtractorFields :
    CompletionExtractorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionExtractorUp.mk G M S D Q E H C P N => [G, M, S, D, Q, E, H, C, P, N]

def completionExtractorToEventFlow :
    CompletionExtractorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (completionExtractorFields x).map completionExtractorEncodeBHist

private def completionExtractorRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => completionExtractorRawAt n rest

private def completionExtractorLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => completionExtractorLengthEq n rest

def completionExtractorFromEventFlow :
    EventFlow → Option CompletionExtractorUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match completionExtractorLengthEq 10 flow with
      | true =>
          some
            (CompletionExtractorUp.mk
              (completionExtractorDecodeBHist (completionExtractorRawAt 0 flow))
              (completionExtractorDecodeBHist (completionExtractorRawAt 1 flow))
              (completionExtractorDecodeBHist (completionExtractorRawAt 2 flow))
              (completionExtractorDecodeBHist (completionExtractorRawAt 3 flow))
              (completionExtractorDecodeBHist (completionExtractorRawAt 4 flow))
              (completionExtractorDecodeBHist (completionExtractorRawAt 5 flow))
              (completionExtractorDecodeBHist (completionExtractorRawAt 6 flow))
              (completionExtractorDecodeBHist (completionExtractorRawAt 7 flow))
              (completionExtractorDecodeBHist (completionExtractorRawAt 8 flow))
              (completionExtractorDecodeBHist (completionExtractorRawAt 9 flow)))
      | false => none

private theorem completionExtractorRoundTrip :
    ∀ x : CompletionExtractorUp,
      completionExtractorFromEventFlow (completionExtractorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G M S D Q E H C P N =>
      change
        some
          (CompletionExtractorUp.mk
            (completionExtractorDecodeBHist (completionExtractorEncodeBHist G))
            (completionExtractorDecodeBHist (completionExtractorEncodeBHist M))
            (completionExtractorDecodeBHist (completionExtractorEncodeBHist S))
            (completionExtractorDecodeBHist (completionExtractorEncodeBHist D))
            (completionExtractorDecodeBHist (completionExtractorEncodeBHist Q))
            (completionExtractorDecodeBHist (completionExtractorEncodeBHist E))
            (completionExtractorDecodeBHist (completionExtractorEncodeBHist H))
            (completionExtractorDecodeBHist (completionExtractorEncodeBHist C))
            (completionExtractorDecodeBHist (completionExtractorEncodeBHist P))
            (completionExtractorDecodeBHist (completionExtractorEncodeBHist N))) =
          some (CompletionExtractorUp.mk G M S D Q E H C P N)
      rw [completionExtractorDecodeEncodeBHist G,
        completionExtractorDecodeEncodeBHist M,
        completionExtractorDecodeEncodeBHist S,
        completionExtractorDecodeEncodeBHist D,
        completionExtractorDecodeEncodeBHist Q,
        completionExtractorDecodeEncodeBHist E,
        completionExtractorDecodeEncodeBHist H,
        completionExtractorDecodeEncodeBHist C,
        completionExtractorDecodeEncodeBHist P,
        completionExtractorDecodeEncodeBHist N]

private theorem completionExtractorToEventFlow_injective
    {x y : CompletionExtractorUp} :
    completionExtractorToEventFlow x = completionExtractorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionExtractorFromEventFlow (completionExtractorToEventFlow x) =
        completionExtractorFromEventFlow (completionExtractorToEventFlow y) :=
    congrArg completionExtractorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (completionExtractorRoundTrip x).symm
      (Eq.trans hread (completionExtractorRoundTrip y)))

private theorem completionExtractorFieldFaithful_proof :
    ∀ x y : CompletionExtractorUp, completionExtractorFields x = completionExtractorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G1 M1 S1 D1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk G2 M2 S2 D2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance completionExtractorBHistCarrier :
    BHistCarrier CompletionExtractorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionExtractorToEventFlow
  fromEventFlow := completionExtractorFromEventFlow

instance completionExtractorChapterTasteGate :
    ChapterTasteGate CompletionExtractorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completionExtractorFromEventFlow (completionExtractorToEventFlow x) = some x
    exact completionExtractorRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (completionExtractorToEventFlow_injective heq)

instance completionExtractorFieldFaithful :
    FieldFaithful CompletionExtractorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := completionExtractorFields
  field_faithful := completionExtractorFieldFaithful_proof

instance completionExtractorNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CompletionExtractorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompletionExtractorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompletionExtractorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompletionExtractorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completionExtractorChapterTasteGate

theorem CompletionExtractorUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompletionExtractorUp) ∧
      Nonempty (FieldFaithful CompletionExtractorUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial CompletionExtractorUp) ∧
      (∀ h : BHist,
        completionExtractorDecodeBHist (completionExtractorEncodeBHist h) = h) ∧
      (∀ x : CompletionExtractorUp,
        completionExtractorFromEventFlow (completionExtractorToEventFlow x) = some x) ∧
      (∀ x y : CompletionExtractorUp,
        completionExtractorToEventFlow x = completionExtractorToEventFlow y → x = y) ∧
      completionExtractorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨Nonempty.intro completionExtractorChapterTasteGate,
      Nonempty.intro completionExtractorFieldFaithful,
      Nonempty.intro completionExtractorNontrivial,
      completionExtractorDecodeEncodeBHist,
      completionExtractorRoundTrip,
      (fun _ _ heq => completionExtractorToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompletionExtractorUp
