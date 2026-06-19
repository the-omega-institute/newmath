import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DedekindEtaCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DedekindEtaCompletionUp : Type where
  | mk (S R D Q L A H C P N : BHist) : DedekindEtaCompletionUp
  deriving DecidableEq

def dedekindEtaCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dedekindEtaCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dedekindEtaCompletionEncodeBHist h

def dedekindEtaCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dedekindEtaCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dedekindEtaCompletionDecodeBHist tail)

private theorem dedekindEtaCompletion_decode_encode_bhist :
    ∀ h : BHist,
      dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dedekindEtaCompletionFields : DedekindEtaCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DedekindEtaCompletionUp.mk S R D Q L A H C P N => [S, R, D, Q, L, A, H, C, P, N]

def dedekindEtaCompletionToEventFlow : DedekindEtaCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DedekindEtaCompletionUp.mk S R D Q L A H C P N =>
      [dedekindEtaCompletionEncodeBHist S,
        dedekindEtaCompletionEncodeBHist R,
        dedekindEtaCompletionEncodeBHist D,
        dedekindEtaCompletionEncodeBHist Q,
        dedekindEtaCompletionEncodeBHist L,
        dedekindEtaCompletionEncodeBHist A,
        dedekindEtaCompletionEncodeBHist H,
        dedekindEtaCompletionEncodeBHist C,
        dedekindEtaCompletionEncodeBHist P,
        dedekindEtaCompletionEncodeBHist N]

private def dedekindEtaCompletionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => dedekindEtaCompletionRawAt n rest

private def dedekindEtaCompletionLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => dedekindEtaCompletionLengthEq n rest

def dedekindEtaCompletionFromEventFlow : EventFlow → Option DedekindEtaCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match dedekindEtaCompletionLengthEq 10 flow with
      | true =>
          some
            (DedekindEtaCompletionUp.mk
              (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionRawAt 0 flow))
              (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionRawAt 1 flow))
              (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionRawAt 2 flow))
              (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionRawAt 3 flow))
              (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionRawAt 4 flow))
              (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionRawAt 5 flow))
              (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionRawAt 6 flow))
              (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionRawAt 7 flow))
              (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionRawAt 8 flow))
              (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionRawAt 9 flow)))
      | false => none

private theorem dedekindEtaCompletion_round_trip :
    ∀ x : DedekindEtaCompletionUp,
      dedekindEtaCompletionFromEventFlow (dedekindEtaCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D Q L A H C P N =>
      change
        some
          (DedekindEtaCompletionUp.mk
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist S))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist R))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist D))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist Q))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist L))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist A))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist H))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist C))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist P))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist N))) =
          some (DedekindEtaCompletionUp.mk S R D Q L A H C P N)
      rw [dedekindEtaCompletion_decode_encode_bhist S,
        dedekindEtaCompletion_decode_encode_bhist R,
        dedekindEtaCompletion_decode_encode_bhist D,
        dedekindEtaCompletion_decode_encode_bhist Q,
        dedekindEtaCompletion_decode_encode_bhist L,
        dedekindEtaCompletion_decode_encode_bhist A,
        dedekindEtaCompletion_decode_encode_bhist H,
        dedekindEtaCompletion_decode_encode_bhist C,
        dedekindEtaCompletion_decode_encode_bhist P,
        dedekindEtaCompletion_decode_encode_bhist N]

private theorem dedekindEtaCompletionToEventFlow_injective
    {x y : DedekindEtaCompletionUp} :
    dedekindEtaCompletionToEventFlow x = dedekindEtaCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dedekindEtaCompletionFromEventFlow (dedekindEtaCompletionToEventFlow x) =
        dedekindEtaCompletionFromEventFlow (dedekindEtaCompletionToEventFlow y) :=
    congrArg dedekindEtaCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dedekindEtaCompletion_round_trip x).symm
      (Eq.trans hread (dedekindEtaCompletion_round_trip y)))

private theorem dedekindEtaCompletion_field_faithful :
    ∀ x y : DedekindEtaCompletionUp,
      dedekindEtaCompletionFields x = dedekindEtaCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S1 R1 D1 Q1 L1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 R2 D2 Q2 L2 A2 H2 C2 P2 N2 =>
          cases h
          rfl

instance dedekindEtaCompletionBHistCarrier : BHistCarrier DedekindEtaCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dedekindEtaCompletionToEventFlow
  fromEventFlow := dedekindEtaCompletionFromEventFlow

instance dedekindEtaCompletionChapterTasteGate :
    ChapterTasteGate DedekindEtaCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dedekindEtaCompletionFromEventFlow (dedekindEtaCompletionToEventFlow x) = some x
    exact dedekindEtaCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dedekindEtaCompletionToEventFlow_injective heq)

instance dedekindEtaCompletionFieldFaithful :
    FieldFaithful DedekindEtaCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dedekindEtaCompletionFields
  field_faithful := dedekindEtaCompletion_field_faithful

instance dedekindEtaCompletionNontrivial : Nontrivial DedekindEtaCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DedekindEtaCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DedekindEtaCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DedekindEtaCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dedekindEtaCompletionChapterTasteGate

theorem DedekindEtaCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist h) = h) ∧
      (∀ x : DedekindEtaCompletionUp,
        dedekindEtaCompletionFromEventFlow (dedekindEtaCompletionToEventFlow x) = some x) ∧
        (∀ x y : DedekindEtaCompletionUp,
          dedekindEtaCompletionToEventFlow x = dedekindEtaCompletionToEventFlow y → x = y) ∧
          dedekindEtaCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨dedekindEtaCompletion_decode_encode_bhist,
      dedekindEtaCompletion_round_trip,
      by
        intro x y heq
        exact dedekindEtaCompletionToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.DedekindEtaCompletionUp
