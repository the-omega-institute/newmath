import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PostMedianGateShellUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PostMedianGateShellUp : Type where
  | mk
      (codonShell booleanCoordinate spectralOptimum firstExit transport replay provenance
        name : BHist) :
      PostMedianGateShellUp
  deriving DecidableEq

def postMedianGateShellEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: postMedianGateShellEncodeBHist h
  | BHist.e1 h => BMark.b1 :: postMedianGateShellEncodeBHist h

def postMedianGateShellDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (postMedianGateShellDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (postMedianGateShellDecodeBHist tail)

private theorem PostMedianGateShellTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      postMedianGateShellDecodeBHist (postMedianGateShellEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def postMedianGateShellFields : PostMedianGateShellUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PostMedianGateShellUp.mk codonShell booleanCoordinate spectralOptimum firstExit
      transport replay provenance name =>
      [codonShell, booleanCoordinate, spectralOptimum, firstExit, transport, replay,
        provenance, name]

def postMedianGateShellToEventFlow : PostMedianGateShellUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (postMedianGateShellFields x).map postMedianGateShellEncodeBHist

private def postMedianGateShellEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      postMedianGateShellEventAtDefault index rest

def postMedianGateShellFromEventFlow
    (ef : EventFlow) : Option PostMedianGateShellUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PostMedianGateShellUp.mk
      (postMedianGateShellDecodeBHist (postMedianGateShellEventAtDefault 0 ef))
      (postMedianGateShellDecodeBHist (postMedianGateShellEventAtDefault 1 ef))
      (postMedianGateShellDecodeBHist (postMedianGateShellEventAtDefault 2 ef))
      (postMedianGateShellDecodeBHist (postMedianGateShellEventAtDefault 3 ef))
      (postMedianGateShellDecodeBHist (postMedianGateShellEventAtDefault 4 ef))
      (postMedianGateShellDecodeBHist (postMedianGateShellEventAtDefault 5 ef))
      (postMedianGateShellDecodeBHist (postMedianGateShellEventAtDefault 6 ef))
      (postMedianGateShellDecodeBHist (postMedianGateShellEventAtDefault 7 ef)))

private theorem PostMedianGateShellTasteGate_single_carrier_alignment_round_trip
    (x : PostMedianGateShellUp) :
    postMedianGateShellFromEventFlow (postMedianGateShellToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk codonShell booleanCoordinate spectralOptimum firstExit transport replay provenance name =>
      change
        some
          (PostMedianGateShellUp.mk
            (postMedianGateShellDecodeBHist (postMedianGateShellEncodeBHist codonShell))
            (postMedianGateShellDecodeBHist
              (postMedianGateShellEncodeBHist booleanCoordinate))
            (postMedianGateShellDecodeBHist
              (postMedianGateShellEncodeBHist spectralOptimum))
            (postMedianGateShellDecodeBHist (postMedianGateShellEncodeBHist firstExit))
            (postMedianGateShellDecodeBHist (postMedianGateShellEncodeBHist transport))
            (postMedianGateShellDecodeBHist (postMedianGateShellEncodeBHist replay))
            (postMedianGateShellDecodeBHist (postMedianGateShellEncodeBHist provenance))
            (postMedianGateShellDecodeBHist (postMedianGateShellEncodeBHist name))) =
          some
            (PostMedianGateShellUp.mk codonShell booleanCoordinate spectralOptimum
              firstExit transport replay provenance name)
      rw [PostMedianGateShellTasteGate_single_carrier_alignment_decode_encode codonShell,
        PostMedianGateShellTasteGate_single_carrier_alignment_decode_encode booleanCoordinate,
        PostMedianGateShellTasteGate_single_carrier_alignment_decode_encode spectralOptimum,
        PostMedianGateShellTasteGate_single_carrier_alignment_decode_encode firstExit,
        PostMedianGateShellTasteGate_single_carrier_alignment_decode_encode transport,
        PostMedianGateShellTasteGate_single_carrier_alignment_decode_encode replay,
        PostMedianGateShellTasteGate_single_carrier_alignment_decode_encode provenance,
        PostMedianGateShellTasteGate_single_carrier_alignment_decode_encode name]

private theorem PostMedianGateShellTasteGate_single_carrier_alignment_injective
    {x y : PostMedianGateShellUp} :
    postMedianGateShellToEventFlow x = postMedianGateShellToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      postMedianGateShellFromEventFlow (postMedianGateShellToEventFlow x) =
        postMedianGateShellFromEventFlow (postMedianGateShellToEventFlow y) :=
    congrArg postMedianGateShellFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PostMedianGateShellTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PostMedianGateShellTasteGate_single_carrier_alignment_round_trip y)))

private theorem PostMedianGateShellTasteGate_single_carrier_alignment_fields :
    ∀ x y : PostMedianGateShellUp,
      postMedianGateShellFields x = postMedianGateShellFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk codonShell₁ booleanCoordinate₁ spectralOptimum₁ firstExit₁ transport₁ replay₁
      provenance₁ name₁ =>
      cases y with
      | mk codonShell₂ booleanCoordinate₂ spectralOptimum₂ firstExit₂ transport₂ replay₂
          provenance₂ name₂ =>
          cases hfields
          rfl

instance postMedianGateShellBHistCarrier : BHistCarrier PostMedianGateShellUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := postMedianGateShellToEventFlow
  fromEventFlow := postMedianGateShellFromEventFlow

instance postMedianGateShellChapterTasteGate :
    ChapterTasteGate PostMedianGateShellUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change postMedianGateShellFromEventFlow (postMedianGateShellToEventFlow x) = some x
    exact PostMedianGateShellTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PostMedianGateShellTasteGate_single_carrier_alignment_injective heq)

instance postMedianGateShellFieldFaithful : FieldFaithful PostMedianGateShellUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := postMedianGateShellFields
  field_faithful := PostMedianGateShellTasteGate_single_carrier_alignment_fields

instance postMedianGateShellNontrivial :
    BEDC.Meta.TasteGate.Nontrivial PostMedianGateShellUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PostMedianGateShellUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PostMedianGateShellUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def PostMedianGateShellTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate PostMedianGateShellUp :=
  -- BEDC touchpoint anchor: BHist BMark
  postMedianGateShellChapterTasteGate

theorem PostMedianGateShellTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      postMedianGateShellDecodeBHist (postMedianGateShellEncodeBHist h) = h) ∧
      (∀ x : PostMedianGateShellUp,
        postMedianGateShellFromEventFlow (postMedianGateShellToEventFlow x) = some x) ∧
        (∀ x y : PostMedianGateShellUp,
          postMedianGateShellToEventFlow x = postMedianGateShellToEventFlow y → x = y) ∧
          postMedianGateShellEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact PostMedianGateShellTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact PostMedianGateShellTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact PostMedianGateShellTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.PostMedianGateShellUp
