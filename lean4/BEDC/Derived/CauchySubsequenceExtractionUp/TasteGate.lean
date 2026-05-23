import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySubsequenceExtractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySubsequenceExtractionUp : Type where
  | mk (S M D I W R H C P N : BHist) : CauchySubsequenceExtractionUp
  deriving DecidableEq

def cauchySubsequenceExtractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySubsequenceExtractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySubsequenceExtractionEncodeBHist h

def cauchySubsequenceExtractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySubsequenceExtractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySubsequenceExtractionDecodeBHist tail)

private theorem CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchySubsequenceExtractionDecodeBHist
        (cauchySubsequenceExtractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySubsequenceExtractionFields : CauchySubsequenceExtractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySubsequenceExtractionUp.mk S M D I W R H C P N => [S, M, D, I, W, R, H, C, P, N]

def cauchySubsequenceExtractionToEventFlow : CauchySubsequenceExtractionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySubsequenceExtractionFields x).map cauchySubsequenceExtractionEncodeBHist

private def cauchySubsequenceExtractionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySubsequenceExtractionEventAt index rest

def cauchySubsequenceExtractionFromEventFlow (ef : EventFlow) :
    Option CauchySubsequenceExtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchySubsequenceExtractionUp.mk
      (cauchySubsequenceExtractionDecodeBHist (cauchySubsequenceExtractionEventAt 0 ef))
      (cauchySubsequenceExtractionDecodeBHist (cauchySubsequenceExtractionEventAt 1 ef))
      (cauchySubsequenceExtractionDecodeBHist (cauchySubsequenceExtractionEventAt 2 ef))
      (cauchySubsequenceExtractionDecodeBHist (cauchySubsequenceExtractionEventAt 3 ef))
      (cauchySubsequenceExtractionDecodeBHist (cauchySubsequenceExtractionEventAt 4 ef))
      (cauchySubsequenceExtractionDecodeBHist (cauchySubsequenceExtractionEventAt 5 ef))
      (cauchySubsequenceExtractionDecodeBHist (cauchySubsequenceExtractionEventAt 6 ef))
      (cauchySubsequenceExtractionDecodeBHist (cauchySubsequenceExtractionEventAt 7 ef))
      (cauchySubsequenceExtractionDecodeBHist (cauchySubsequenceExtractionEventAt 8 ef))
      (cauchySubsequenceExtractionDecodeBHist (cauchySubsequenceExtractionEventAt 9 ef)))

private theorem CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_round_trip
    (x : CauchySubsequenceExtractionUp) :
    cauchySubsequenceExtractionFromEventFlow (cauchySubsequenceExtractionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S M D I W R H C P N =>
      change
        some
          (CauchySubsequenceExtractionUp.mk
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist S))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist M))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist D))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist I))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist W))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist R))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist H))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist C))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist P))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist N))) =
          some (CauchySubsequenceExtractionUp.mk S M D I W R H C P N)
      rw [CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_decode_encode S,
        CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_decode_encode M,
        CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_decode_encode D,
        CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_decode_encode I,
        CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_decode_encode W,
        CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_decode_encode R,
        CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_decode_encode H,
        CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_decode_encode C,
        CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_decode_encode P,
        CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchySubsequenceExtractionUp} :
    cauchySubsequenceExtractionToEventFlow x =
      cauchySubsequenceExtractionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySubsequenceExtractionFromEventFlow (cauchySubsequenceExtractionToEventFlow x) =
        cauchySubsequenceExtractionFromEventFlow (cauchySubsequenceExtractionToEventFlow y) :=
    congrArg cauchySubsequenceExtractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchySubsequenceExtractionUp,
      cauchySubsequenceExtractionFields x = cauchySubsequenceExtractionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 M1 D1 I1 W1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 M2 D2 I2 W2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchySubsequenceExtractionBHistCarrier :
    BHistCarrier CauchySubsequenceExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySubsequenceExtractionToEventFlow
  fromEventFlow := cauchySubsequenceExtractionFromEventFlow

instance cauchySubsequenceExtractionChapterTasteGate :
    ChapterTasteGate CauchySubsequenceExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySubsequenceExtractionFromEventFlow
      (cauchySubsequenceExtractionToEventFlow x) = some x
    exact CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchySubsequenceExtractionFieldFaithful :
    FieldFaithful CauchySubsequenceExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchySubsequenceExtractionFields
  field_faithful := CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_fields

instance cauchySubsequenceExtractionNontrivial :
    Nontrivial CauchySubsequenceExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchySubsequenceExtractionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchySubsequenceExtractionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchySubsequenceExtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySubsequenceExtractionChapterTasteGate

theorem CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchySubsequenceExtractionDecodeBHist
        (cauchySubsequenceExtractionEncodeBHist h) = h) ∧
      (∀ x : CauchySubsequenceExtractionUp,
        cauchySubsequenceExtractionFromEventFlow
          (cauchySubsequenceExtractionToEventFlow x) = some x) ∧
        (∀ x y : CauchySubsequenceExtractionUp,
          cauchySubsequenceExtractionToEventFlow x =
            cauchySubsequenceExtractionToEventFlow y → x = y) ∧
          cauchySubsequenceExtractionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_decode_encode,
      CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchySubsequenceExtractionUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchySubsequenceExtractionUp
