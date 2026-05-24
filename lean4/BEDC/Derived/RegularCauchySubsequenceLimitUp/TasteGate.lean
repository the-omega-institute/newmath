import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySubsequenceLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySubsequenceLimitUp : Type where
  | mk (S L W R D E H C P N : BHist) : RegularCauchySubsequenceLimitUp
  deriving DecidableEq

def regularCauchySubsequenceLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySubsequenceLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySubsequenceLimitEncodeBHist h

def regularCauchySubsequenceLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySubsequenceLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySubsequenceLimitDecodeBHist tail)

private theorem RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchySubsequenceLimitDecodeBHist
        (regularCauchySubsequenceLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySubsequenceLimitFields :
    RegularCauchySubsequenceLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySubsequenceLimitUp.mk S L W R D E H C P N =>
      [S, L, W, R, D, E, H, C, P, N]

def regularCauchySubsequenceLimitToEventFlow :
    RegularCauchySubsequenceLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchySubsequenceLimitFields x).map
      regularCauchySubsequenceLimitEncodeBHist

private def regularCauchySubsequenceLimitEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchySubsequenceLimitEventAt index rest

def regularCauchySubsequenceLimitFromEventFlow (ef : EventFlow) :
    Option RegularCauchySubsequenceLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchySubsequenceLimitUp.mk
      (regularCauchySubsequenceLimitDecodeBHist (regularCauchySubsequenceLimitEventAt 0 ef))
      (regularCauchySubsequenceLimitDecodeBHist (regularCauchySubsequenceLimitEventAt 1 ef))
      (regularCauchySubsequenceLimitDecodeBHist (regularCauchySubsequenceLimitEventAt 2 ef))
      (regularCauchySubsequenceLimitDecodeBHist (regularCauchySubsequenceLimitEventAt 3 ef))
      (regularCauchySubsequenceLimitDecodeBHist (regularCauchySubsequenceLimitEventAt 4 ef))
      (regularCauchySubsequenceLimitDecodeBHist (regularCauchySubsequenceLimitEventAt 5 ef))
      (regularCauchySubsequenceLimitDecodeBHist (regularCauchySubsequenceLimitEventAt 6 ef))
      (regularCauchySubsequenceLimitDecodeBHist (regularCauchySubsequenceLimitEventAt 7 ef))
      (regularCauchySubsequenceLimitDecodeBHist (regularCauchySubsequenceLimitEventAt 8 ef))
      (regularCauchySubsequenceLimitDecodeBHist (regularCauchySubsequenceLimitEventAt 9 ef)))

private theorem RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchySubsequenceLimitUp) :
    regularCauchySubsequenceLimitFromEventFlow
      (regularCauchySubsequenceLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S L W R D E H C P N =>
      change
        some
          (RegularCauchySubsequenceLimitUp.mk
            (regularCauchySubsequenceLimitDecodeBHist
              (regularCauchySubsequenceLimitEncodeBHist S))
            (regularCauchySubsequenceLimitDecodeBHist
              (regularCauchySubsequenceLimitEncodeBHist L))
            (regularCauchySubsequenceLimitDecodeBHist
              (regularCauchySubsequenceLimitEncodeBHist W))
            (regularCauchySubsequenceLimitDecodeBHist
              (regularCauchySubsequenceLimitEncodeBHist R))
            (regularCauchySubsequenceLimitDecodeBHist
              (regularCauchySubsequenceLimitEncodeBHist D))
            (regularCauchySubsequenceLimitDecodeBHist
              (regularCauchySubsequenceLimitEncodeBHist E))
            (regularCauchySubsequenceLimitDecodeBHist
              (regularCauchySubsequenceLimitEncodeBHist H))
            (regularCauchySubsequenceLimitDecodeBHist
              (regularCauchySubsequenceLimitEncodeBHist C))
            (regularCauchySubsequenceLimitDecodeBHist
              (regularCauchySubsequenceLimitEncodeBHist P))
            (regularCauchySubsequenceLimitDecodeBHist
              (regularCauchySubsequenceLimitEncodeBHist N))) =
          some (RegularCauchySubsequenceLimitUp.mk S L W R D E H C P N)
      rw [RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_decode_encode L,
        RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchySubsequenceLimitUp} :
    regularCauchySubsequenceLimitToEventFlow x =
      regularCauchySubsequenceLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySubsequenceLimitFromEventFlow
          (regularCauchySubsequenceLimitToEventFlow x) =
        regularCauchySubsequenceLimitFromEventFlow
          (regularCauchySubsequenceLimitToEventFlow y) :=
    congrArg regularCauchySubsequenceLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchySubsequenceLimitBHistCarrier :
    BHistCarrier RegularCauchySubsequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySubsequenceLimitToEventFlow
  fromEventFlow := regularCauchySubsequenceLimitFromEventFlow

instance regularCauchySubsequenceLimitChapterTasteGate :
    ChapterTasteGate RegularCauchySubsequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySubsequenceLimitFromEventFlow
        (regularCauchySubsequenceLimitToEventFlow x) = some x
    exact RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchySubsequenceLimitFieldFaithful :
    FieldFaithful RegularCauchySubsequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchySubsequenceLimitFields
  field_faithful := by
    intro x y hfields
    cases x with
    | mk S L W R D E H C P N =>
        cases y with
        | mk S' L' W' R' D' E' H' C' P' N' =>
            cases hfields
            rfl

instance regularCauchySubsequenceLimitNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchySubsequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchySubsequenceLimitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchySubsequenceLimitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchySubsequenceLimitUp) ∧
      Nonempty (FieldFaithful RegularCauchySubsequenceLimitUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchySubsequenceLimitUp) ∧
      (∀ h : BHist,
        regularCauchySubsequenceLimitDecodeBHist
          (regularCauchySubsequenceLimitEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySubsequenceLimitUp,
        regularCauchySubsequenceLimitFromEventFlow
          (regularCauchySubsequenceLimitToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchySubsequenceLimitUp,
        regularCauchySubsequenceLimitToEventFlow x =
          regularCauchySubsequenceLimitToEventFlow y → x = y) ∧
      regularCauchySubsequenceLimitEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨regularCauchySubsequenceLimitChapterTasteGate⟩
  constructor
  · exact ⟨regularCauchySubsequenceLimitFieldFaithful⟩
  constructor
  · exact ⟨regularCauchySubsequenceLimitNontrivial⟩
  constructor
  · exact RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact RegularCauchySubsequenceLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.RegularCauchySubsequenceLimitUp
